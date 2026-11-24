module

public import RiemannMasullo.AppC_LCTVS.Sec2a_part2
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.Seminorm.DirectSum
public import Mathlib.Analysis.LocallyConvex.Montel
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Data.Set.FiniteExhaustion
import all RiemannMasullo.AppC_LCTVS.Sec1
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.Dual
import RiemannMasullo.ForMathlib.Analysis.Normed.Operator.AbsolutelySumming.Composition
import RiemannMasullo.ForMathlib.Analysis.Normed.Operator.Compact.Hilbert
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.Seminorm.DirectSum
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.WeakDual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.WithSeminorms
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Nuclear spaces and the finest locally convex topology

Masullo, Appendix C, §§C.2.4–C.2.5. At the end we state the results of §C.1 that
require nuclearity. As in the preceding sections, `PolynormableSpace ℂ` expresses
local convexity for the complex vector topology.
-/

@[expose] public noncomputable section

open Set Filter Topology Bornology UniformSpace TensorProduct MeasureTheory
open scoped TensorProduct DirectSum UniformConvergence UniformConvergenceCLM Cardinal

namespace RiemannMasullo

universe v u w

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

local instance {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [ContinuousSMul ℂ E] : ContinuousSMul ℝ E :=
  MulAction.continuousSMul_compHom (f := (algebraMap ℝ ℂ).toMonoidHom) Complex.continuous_ofReal

/-! ## Nuclear spaces -/

-- The continuity of (C.2.4.1) is already stated in `continuous_projectiveTensor_to_injectiveTensor`.

/-- Paper: Definition C.2.4.1, p. 685. A Hausdorff locally convex space is nuclear
when the linear identity from the projective to the injective tensor product is a
homeomorphism for every Hausdorff locally convex test space.
Deviation: The test-space universe is at least the universe of the given space and
can be raised by an independent universe parameter. -/
def IsNuclearTVS.{test, carrier} (E : Type carrier) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  T2Space E ∧ PolynormableSpace ℂ E ∧
    ∀ (F : Type (max test carrier)) (_ : AddCommGroup F) (_ : Module ℂ F) (_ : TopologicalSpace F)
      (_ : PolynormableSpace ℂ F) (_ : T2Space F),
      @IsHomeomorph (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id

section FiniteDimensionalNuclearity

open scoped Pointwise

variable {E : Type*} {F : Type w} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]

/-- Paper: (C.2.3.7), p. 677. Evaluations against the two polars are bounded on each
tensor, and their supremum is the generating injective seminorm. -/
private theorem injectiveSeminorm_eq_ciSup
    (U : {U : Set E // U ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0}) (z : E ⊗[ℂ] F) :
    let D := (StrongDual.polar ℂ U.val : Type _) × (StrongDual.polar ℂ V.val : Type _)
    BddAbove (range fun f : D ↦ ‖tensorDualForm f.1.val f.2.val z‖) ∧
      injectiveTensorSeminorm U V z = ⨆ f : D, ‖tensorDualForm f.1.val f.2.val z‖ := by
  intro D
  have hbound (z : E ⊗[ℂ] F) :
      ∃ C : ℝ, ∀ (φ : StrongDual.polar ℂ U.val) (ψ : StrongDual.polar ℂ V.val),
        ‖tensorDualForm φ.val ψ.val z‖ ≤ C := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        obtain ⟨a, hx⟩ : ∃ a : ℂ, x ∈ a • U.val := by
          simpa using (absorbent_nhds_zero (𝕜 := ℂ) U.property x).exists
        obtain ⟨b, hy⟩ : ∃ b : ℂ, y ∈ b • V.val := by
          simpa using (absorbent_nhds_zero (𝕜 := ℂ) V.property y).exists
        obtain ⟨x', hx', rfl⟩ := hx
        obtain ⟨y', hy', rfl⟩ := hy
        refine ⟨‖a‖ * ‖b‖, fun φ ψ ↦ ?_⟩
        have hφ := (StrongDual.mem_polar_iff ℂ _).mp φ.property _ hx'
        have hψ := (StrongDual.mem_polar_iff ℂ _).mp ψ.property _ hy'
        simp only [tensorDualForm_tmul, map_smul, norm_mul, norm_smul]
        gcongr
        · exact mul_le_of_le_one_right (norm_nonneg _) hφ
        · exact mul_le_of_le_one_right (norm_nonneg _) hψ
    | add z₁ z₂ h₁ h₂ =>
        obtain ⟨C₁, h₁⟩ := h₁
        obtain ⟨C₂, h₂⟩ := h₂
        refine ⟨C₁ + C₂, fun φ ψ ↦ ?_⟩
        rw [map_add]
        exact (norm_add_le _ _).trans (add_le_add (h₁ φ ψ) (h₂ φ ψ))
  have hBdd (z : E ⊗[ℂ] F) :
      BddAbove (range fun f : StrongDual.polar ℂ U.val × StrongDual.polar ℂ V.val ↦
        ‖tensorDualForm f.1.val f.2.val z‖) := by
    obtain ⟨C, hC⟩ := hbound z
    exact ⟨C, forall_mem_range.mpr fun f ↦ hC f.1 f.2⟩
  have hSeminorm : BddAbove (range fun f : D ↦
      (normSeminorm ℂ ℂ).comp (tensorDualForm f.1.val f.2.val)) :=
    Seminorm.bddAbove_range_iff.mpr hBdd
  refine ⟨hBdd z, ?_⟩
  unfold injectiveTensorSeminorm
  rw [← ciSup_prod hSeminorm, Seminorm.iSup_apply hSeminorm]
  rfl

/-- Paper: §C.2.3.2, p. 679. Each injective generator is a projective generator,
by scaling one of the two zero-neighborhoods in the polar bound. -/
private theorem injectiveSeminorm_continuousAt_tmul
    (U : {U : Set E // U ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0}) :
    ContinuousAt (fun v : E × F ↦ injectiveTensorSeminorm U V (v.1 ⊗ₜ[ℂ] v.2)) 0 := by
  have : Nonempty (StrongDual.polar ℂ U.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  have : Nonempty (StrongDual.polar ℂ V.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  rw [ContinuousAt, show injectiveTensorSeminorm U V ((0 : E × F).1 ⊗ₜ[ℂ]
    (0 : E × F).2) = 0 by simp, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨c, hc, hcε⟩ := NormedField.exists_norm_lt ℂ hε
  have hV : c • V.val ∈ 𝓝 (0 : F) := by
    simpa using smul_mem_nhds_smul₀ (norm_pos_iff.mp hc) V.property
  have hUV : U.val ×ˢ (c • V.val) ∈ 𝓝 (0 : E × F) :=
    (nhds_prod_eq (x := (0 : E)) (y := (0 : F))).symm ▸ prod_mem_prod U.property hV
  filter_upwards [hUV] with z hz
  rw [dist_zero_right, Real.norm_of_nonneg (apply_nonneg _ _)]
  refine lt_of_le_of_lt ?_ hcε
  rw [(injectiveSeminorm_eq_ciSup U V _).2]
  apply ciSup_le
  rintro ⟨φ, ψ⟩
  obtain ⟨y, hy, hcy⟩ := hz.2
  have hφ := (StrongDual.mem_polar_iff ℂ _).mp φ.property _ hz.1
  have hψ := (StrongDual.mem_polar_iff ℂ _).mp ψ.property _ hy
  rw [tensorDualForm_tmul, ← hcy, map_smul, norm_mul, norm_smul]
  calc
    _ ≤ 1 * (‖c‖ * 1) := by gcongr
    _ = ‖c‖ := by simp

/-- Paper: §C.2.3.2, p. 679. Tensoring with a fixed vector is continuous for the
projective topology. -/
theorem continuous_projectiveTensor_tmul_left (x : E) :
    Continuous (show F → ProjectiveTensor E F from TensorProduct.mk ℂ E F x) := by
  have := PolynormableSpace.isTopologicalAddGroup ℂ F
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
      ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
  refine hP.continuous_of_continuous_comp (TensorProduct.mk ℂ E F x) fun ⟨p, hp⟩ ↦ ?_
  have h : {z : E × F | p (z.1 ⊗ₜ[ℂ] z.2) < 1} ∈ 𝓝 0 :=
    hp.preimage_mem_nhds (show Iio (1 : ℝ) ∈ 𝓝 (p ((0 : E × F).1 ⊗ₜ[ℂ]
      (0 : E × F).2)) by simpa using Iio_mem_nhds one_pos)
  rw [show (0 : E × F) = ((0 : E), (0 : F)) from rfl, nhds_prod_eq] at h
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp h
  obtain ⟨a, ha⟩ : ∃ a : ℂ, x ∈ a • U := by
    simpa using (absorbent_nhds_zero (𝕜 := ℂ) hU x).exists
  obtain ⟨x', hx', rfl⟩ := ha
  apply Seminorm.continuous' (r := ‖a‖)
  refine Filter.mem_of_superset hV fun y hy ↦ ?_
  rw [Seminorm.mem_closedBall_zero]
  change p ((a • x') ⊗ₜ[ℂ] y) ≤ ‖a‖
  rw [← smul_tmul', map_smul_eq_mul]
  have hp' : p (x' ⊗ₜ[ℂ] y) < 1 := hUV (a := (x', y)) ⟨hx', hy⟩
  exact mul_le_of_le_one_right (norm_nonneg _) hp'.le

/-- Paper: (C.2.3.6), p. 677. Contracting the first factor with a continuous
functional is continuous for the injective topology. -/
private theorem continuous_injectiveTensor_contract (φ : StrongDual ℂ E) :
    Continuous (show InjectiveTensor E F → F from
      (TensorProduct.lid ℂ F).toLinearMap.comp (φ.toLinearMap.rTensor F)) := by
  let T : E ⊗[ℂ] F →ₗ[ℂ] F :=
    (TensorProduct.lid ℂ F).toLinearMap.comp (φ.toLinearMap.rTensor F)
  have hT (ψ : StrongDual ℂ F) (z : E ⊗[ℂ] F) :
      ψ (T z) = tensorDualForm φ ψ z := by
    have hEq : ψ.toLinearMap.comp T = tensorDualForm φ ψ := by
      apply TensorProduct.ext'
      intro x y
      simp [T, LinearMap.comp_apply, tensorDualForm_tmul, smul_eq_mul]
    exact DFunLike.congr_fun hEq z
  refine (PolynormableSpace.withSeminorms ℂ F).continuous_of_continuous_comp
    (show InjectiveTensor E F →ₗ[ℂ] F from T) fun ⟨q, hq⟩ ↦ ?_
  let p := (normSeminorm ℂ ℂ).comp φ.toLinearMap
  let U : {U : Set E // U ∈ 𝓝 0} :=
    ⟨p.closedBall 0 1, Filter.mem_of_superset (p.ball_mem_nhds φ.continuous.norm one_pos)
      (p.ball_subset_closedBall _ _)⟩
  let V : {V : Set F // V ∈ 𝓝 0} :=
    ⟨q.closedBall 0 1, Filter.mem_of_superset (q.ball_mem_nhds hq one_pos)
      (q.ball_subset_closedBall _ _)⟩
  have hφ : φ ∈ StrongDual.polar ℂ U.val :=
    (StrongDual.mem_polar_iff ℂ _).mpr fun _ hx ↦ (Seminorm.mem_closedBall_zero _).mp hx
  refine Seminorm.continuous_of_le
    ((withGeneratingSeminorms_spec (E ⊗[ℂ] F) _).continuous_seminorm (U, V)) fun z ↦ ?_
  change E ⊗[ℂ] F at z
  change q (T z) ≤ injectiveTensorSeminorm U V z
  have norming (G : Type w) [AddCommGroup G] [Module ℂ G] (p : Seminorm ℂ G) (x : G) :
      ∃ g : G →ₗ[ℂ] ℂ, (∀ y, ‖g y‖ ≤ p y) ∧ ‖g x‖ = p x := by
    let : SeminormedAddCommGroup G := p.toSeminormedAddCommGroup
    let : NormedSpace ℂ G := ⟨fun c y ↦ (map_smul_eq_mul p c y).le⟩
    obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' ℂ x
    refine ⟨g.toLinearMap, fun y ↦ (g.le_opNorm y).trans
      (mul_le_of_le_one_left (apply_nonneg p y) hg), ?_⟩
    change ‖g x‖ = p x
    rw [hgx]
    change ‖(p x : ℂ)‖ = p x
    rw [Complex.norm_real, Real.norm_of_nonneg (apply_nonneg p x)]
  obtain ⟨g, hg, hgz⟩ := norming F q (T z)
  have hgcont : Continuous g :=
    (PolynormableSpace.withSeminorms ℂ F).continuous_normedSpace_rng ℂ g
      ⟨{⟨q, hq⟩}, 1, by simpa using (show (normSeminorm ℂ ℂ).comp g ≤ q from hg)⟩
  let ψ : StrongDual ℂ F := ⟨g, hgcont⟩
  have hψ : ψ ∈ StrongDual.polar ℂ V.val :=
    (StrongDual.mem_polar_iff ℂ _).mpr fun y hy ↦ (hg y).trans ((q.mem_closedBall_zero).mp hy)
  obtain ⟨hBdd, hSup⟩ := injectiveSeminorm_eq_ciSup U V z
  rw [← hgz, show g (T z) = ψ (T z) from rfl, hT ψ z, hSup]
  exact le_ciSup hBdd (⟨φ, hφ⟩, ⟨ψ, hψ⟩)

end FiniteDimensionalNuclearity

/-- Paper: Definition C.2.4.1, p. 685. A finite-dimensional Hausdorff locally convex
space is nuclear.
Deviation: This is a check against the finite-dimensional case used on p. 692. -/
theorem isNuclearTVS_of_finiteDimensional (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [T2Space E] [PolynormableSpace ℂ E] [FiniteDimensional ℂ E] :
    IsNuclearTVS.{v, u} E := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro F _ _ _ _ _
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  let b := Module.finBasis ℂ E
  let φ i : StrongDual ℂ E := (b.coord i).toContinuousLinearMap
  let T i : E ⊗[ℂ] F →ₗ[ℂ] F :=
    (TensorProduct.lid ℂ F).toLinearMap.comp ((φ i).toLinearMap.rTensor F)
  -- Reconstruct the tensor from its finitely many basis coordinates.
  have hback : Continuous (show InjectiveTensor E F → ProjectiveTensor E F from id) := by
    let S i : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F :=
      (TensorProduct.mk ℂ E F (b i)).comp (T i)
    have hS : (∑ i, S i) = (LinearMap.id : E ⊗[ℂ] F →ₗ[ℂ] E ⊗[ℂ] F) := by
      apply TensorProduct.ext'
      intro x y
      simp only [LinearMap.sum_apply, S, LinearMap.comp_apply, T, LinearMap.rTensor_tmul,
        LinearEquiv.coe_coe, TensorProduct.lid_tmul, TensorProduct.mk_apply, LinearMap.id_coe, id_eq]
      change (∑ i, b i ⊗ₜ[ℂ] (b.repr x i • y)) = x ⊗ₜ[ℂ] y
      simp_rw [tmul_smul, smul_tmul']
      rw [← sum_tmul, b.sum_repr]
    have hc : Continuous (show InjectiveTensor E F → ProjectiveTensor E F from
        fun z ↦ ∑ i, S i z) :=
      continuous_finsetSum _ fun i _ ↦
        (continuous_projectiveTensor_tmul_left (F := F) (b i)).comp
          (continuous_injectiveTensor_contract (F := F) (φ i))
    refine hc.congr fun z ↦ ?_
    change E ⊗[ℂ] F at z
    change (∑ i, S i z) = z
    rw [← LinearMap.sum_apply, hS]
    rfl
  -- Each injective seminorm occurs in the projective generating family.
  have hfwd : Continuous (show ProjectiveTensor E F → InjectiveTensor E F from id) := by
    let hI := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
        injectiveTensorSeminorm UV.1 UV.2)
    let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
        ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
    exact hI.continuous_of_continuous_comp (LinearMap.id : ProjectiveTensor E F →ₗ[ℂ] InjectiveTensor E F)
      (fun ⟨U, V⟩ ↦ hP.continuous_seminorm ⟨_, injectiveSeminorm_continuousAt_tmul U V⟩)
  let e : ProjectiveTensor E F ≃ₜ InjectiveTensor E F :=
    ⟨Equiv.refl (E ⊗[ℂ] F), hfwd, hback⟩
  exact e.isHomeomorph

section LocalBanach

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- Paper: §C.2.4.2, p. 686. Equip the carrier with the seminorm used to construct
the local Banach space. -/
def WithLocalSeminorm (_p : Seminorm ℂ E) := E

instance (p : Seminorm ℂ E) : SeminormedAddCommGroup (WithLocalSeminorm p) :=
  p.toSeminormedAddCommGroup

instance (p : Seminorm ℂ E) : Module ℂ (WithLocalSeminorm p) :=
  inferInstanceAs (Module ℂ E)

instance (p : Seminorm ℂ E) : NormedSpace ℂ (WithLocalSeminorm p) where
  norm_smul_le c x := le_of_eq (map_smul_eq_mul p c x)

/-- Paper: §C.2.4.2, p. 686. The separated completion for a seminorm is its local
Banach space. For a balanced convex absorbing set we use its Minkowski seminorm. -/
abbrev LocalBanach (p : Seminorm ℂ E) := Completion (WithLocalSeminorm p)

/-- Paper: §C.2.4.2, p. 686. The canonical image in the local Banach space has norm
given by the chosen seminorm. -/
theorem localBanach_norm_coe (p : Seminorm ℂ E) (x : WithLocalSeminorm p) :
    ‖(x : LocalBanach p)‖ = p x :=
  Completion.norm_coe x

/-- Paper: Theorem C.2.4.2(2), p. 686. When the target seminorm is dominated by the
source seminorm, the linear identity extends to a map of the two local Banach spaces. -/
def localBanachMap (p q : Seminorm ℂ E) (h : q ≤ p) : LocalBanach p →L[ℂ] LocalBanach q :=
  let f : WithLocalSeminorm p →ₗ[ℂ] WithLocalSeminorm q := LinearMap.id
  (f.mkContinuousOfExistsBound ⟨1, fun x ↦ (h x).trans_eq (one_mul (p x)).symm⟩).completion

/-- Paper: Theorem C.2.4.2(2), p. 686. The comparison of local Banach spaces sends
the canonical image of each vector to its canonical image for the smaller seminorm. -/
theorem localBanachMap_coe (p q : Seminorm ℂ E) (h : q ≤ p) (x : WithLocalSeminorm p) :
    localBanachMap p q h x = ((show WithLocalSeminorm q from x) : LocalBanach q) := by
  rw [localBanachMap, ContinuousLinearMap.completion_apply_coe]
  rfl

end LocalBanach

section Characterizations

variable (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: §C.2.4.2, p. 686. The canonical map into the local Banach space of a
continuous seminorm is continuous for the original topology. -/
private theorem exists_localBanach_inclusion {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [PolynormableSpace ℂ X] (p : Seminorm ℂ X) (hp : Continuous p) :
    ∃ f : X →L[ℂ] LocalBanach p, ∀ x : X, f x = (show WithLocalSeminorm p from x) := by
  let f : X →ₗ[ℂ] LocalBanach p := Completion.toComplL.toLinearMap.comp LinearMap.id
  refine ⟨⟨f, ?_⟩, fun _ ↦ rfl⟩
  exact (PolynormableSpace.withSeminorms ℂ X).continuous_normedSpace_rng _ f
    ⟨{⟨p, hp⟩}, 1, by
      simpa using (show (normSeminorm ℂ _).comp f ≤ p from
        fun x ↦ (localBanach_norm_coe p x).le)⟩

omit [T2Space E] in
/-- Paper: Theorem C.2.4.2(2), p. 686. Contracting an algebraic tensor against a
functional on a local Banach space is bounded by the injective seminorm of the tensor. -/
private theorem norm_localBanach_contraction_le {F : Type*} [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] [PolynormableSpace ℂ F] {p : Seminorm ℂ E} {s : Seminorm ℂ F}
    (V : {V : Set E // V ∈ 𝓝 0}) (W : {W : Set F // W ∈ 𝓝 0})
    (i : E →L[ℂ] LocalBanach p) (j : F →L[ℂ] LocalBanach s)
    (hi : ∀ x ∈ V.val, ‖i x‖ ≤ 1) (hj : ∀ y ∈ W.val, ‖j y‖ ≤ 1)
    (φ : LocalBanach p →L[ℂ] ℂ) (z : E ⊗[ℂ] F) :
    ‖((TensorProduct.lid ℂ (LocalBanach s)).toLinearMap.comp
      (TensorProduct.map (φ.comp i).toLinearMap j.toLinearMap)) z‖ ≤
        ‖φ‖ * injectiveTensorSeminorm V W z := by
  let contract (ψ : LocalBanach p →L[ℂ] ℂ) :=
    (TensorProduct.lid ℂ (LocalBanach s)).toLinearMap.comp
      (TensorProduct.map (ψ.comp i).toLinearMap j.toLinearMap)
  change ‖contract φ z‖ ≤ _
  have unit (ψ : LocalBanach p →L[ℂ] ℂ) (hψ : ‖ψ‖ ≤ 1) :
      ‖contract ψ z‖ ≤ injectiveTensorSeminorm V W z := by
    obtain ⟨g, hg, hgz⟩ := exists_dual_vector'' ℂ (contract ψ z)
    have hψV : ψ.comp i ∈ StrongDual.polar ℂ V.val :=
      (StrongDual.mem_polar_iff ℂ _).mpr fun x hx ↦
        (ψ.le_opNorm (i x)).trans (by simpa using mul_le_mul hψ (hi x hx) (norm_nonneg _) zero_le_one)
    have hgW : g.comp j ∈ StrongDual.polar ℂ W.val :=
      (StrongDual.mem_polar_iff ℂ _).mpr fun y hy ↦
        (g.le_opNorm (j y)).trans (by simpa using mul_le_mul hg (hj y hy) (norm_nonneg _) zero_le_one)
    have heq : g.toLinearMap.comp (contract ψ) = tensorDualForm (ψ.comp i) (g.comp j) := by
      apply TensorProduct.ext'
      intro x y
      simp [contract, tensorDualForm_tmul, smul_eq_mul]
    have heqz := DFunLike.congr_fun heq z
    change g (contract ψ z) = _ at heqz
    rw [hgz] at heqz
    obtain ⟨hBdd, hSup⟩ := injectiveSeminorm_eq_ciSup V W z
    rw [hSup]
    have h := le_ciSup hBdd (⟨ψ.comp i, hψV⟩, ⟨g.comp j, hgW⟩)
    change ‖tensorDualForm (ψ.comp i) (g.comp j) z‖ ≤ _ at h
    rw [← heqz] at h
    change ‖(‖contract ψ z‖ : ℂ)‖ ≤ _ at h
    simpa only [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] using h
  by_cases hφ : φ = 0
  · subst φ
    have hz : contract 0 = 0 := by ext x y; simp [contract]
    simp [hz]
  let a : ℂ := ‖φ‖
  have ha : a ≠ 0 := by simpa [a] using hφ
  have hnorm : ‖a‖ = ‖φ‖ := by simp [a]
  let ψ := a⁻¹ • φ
  have hψ : ‖ψ‖ ≤ 1 := by
    rw [norm_smul, norm_inv, hnorm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hφ)]
  have heq : contract φ = a • contract ψ := by
    apply TensorProduct.ext'
    intro x y
    simp [contract, ψ, smul_smul, ha]
  rw [heq, LinearMap.smul_apply, norm_smul, hnorm]
  exact mul_le_mul_of_nonneg_left (unit ψ hψ) (norm_nonneg _)

omit [T2Space E] in
/-- Paper: Theorem C.2.4.2(2), p. 686. A local nuclear series bounds each projective
seminorm with the injective seminorm from the source neighborhood and the second factor. -/
private theorem projectiveSeminorm_le_of_localBanach_series {F : Type*}
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]
    {p q : Seminorm ℂ E} {s : Seminorm ℂ F} (hq : q ≤ p)
    (V : {V : Set E // V ∈ 𝓝 0}) (W : {W : Set F // W ∈ 𝓝 0})
    (i : E →L[ℂ] LocalBanach p) (j : F →L[ℂ] LocalBanach s)
    (hi : ∀ x : E, i x = (show WithLocalSeminorm p from x))
    (hj : ∀ y : F, j y = (show WithLocalSeminorm s from y))
    (hiV : ∀ x ∈ V.val, p x ≤ 1) (hjW : ∀ y ∈ W.val, s y ≤ 1)
    (r : Seminorm ℂ (E ⊗[ℂ] F)) (hr : ∀ x y, r (x ⊗ₜ[ℂ] y) ≤ q x * s y)
    (c : ℕ → ℂ) (φ : ℕ → LocalBanach p →L[ℂ] ℂ) (b : ℕ → LocalBanach q)
    (hc : Summable (fun n ↦ ‖c n‖)) (hφ : Tendsto φ atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0))
    (hseries : ∀ x, HasSum (fun n ↦ (c n * φ n x) • b n) (localBanachMap p q hq x)) :
    ∃ C : ℝ, ∀ z, r z ≤ C * injectiveTensorSeminorm V W z := by
  let κ : E ⊗[ℂ] F →ₗ[ℂ] LocalBanach r := Completion.toComplL.toLinearMap.comp LinearMap.id
  have hκ (z : E ⊗[ℂ] F) : ‖κ z‖ = r z := localBanach_norm_coe r z
  -- Extend the pure-tensor map to both local completions, with values in the completion for r.
  let B₀ : WithLocalSeminorm q →L[ℂ] WithLocalSeminorm s →L[ℂ] LocalBanach r :=
    ((LinearMap.compr₂ (TensorProduct.mk ℂ E F) κ :
        WithLocalSeminorm q →ₗ[ℂ] WithLocalSeminorm s →ₗ[ℂ] LocalBanach r)).mkContinuous₂ 1
      (fun x y ↦ by
        change ‖κ (x ⊗ₜ[ℂ] y)‖ ≤ 1 * q x * s y
        rw [hκ, one_mul]
        exact hr x y)
  let B₁ := B₀.fromCompletion
  let B : LocalBanach q →L[ℂ] LocalBanach s →L[ℂ] LocalBanach r :=
    ((B₁.flip.fromCompletion).flip)
  have hB₀ : ‖B₀‖ ≤ 1 := LinearMap.mkContinuous₂_norm_le _ zero_le_one _
  have hB (x : LocalBanach q) (y : LocalBanach s) : ‖B x y‖ ≤ ‖x‖ * ‖y‖ := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      induction y using Completion.induction_on with
      | hp => exact isClosed_le (by fun_prop) (by fun_prop)
      | ih y =>
        change ‖(B₁.flip.fromCompletion (y : LocalBanach s)) (x : LocalBanach q)‖ ≤ _
        rw [ContinuousLinearMap.fromCompletion_apply_coe, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.fromCompletion_apply_coe, Completion.norm_coe, Completion.norm_coe]
        exact (B₀.le_opNorm₂ x y).trans
          (by calc
            ‖B₀‖ * ‖x‖ * ‖y‖ ≤ 1 * ‖x‖ * ‖y‖ := by gcongr
            _ = _ := by rw [one_mul])
  let D (n : ℕ) : E ⊗[ℂ] F →ₗ[ℂ] LocalBanach s :=
    (TensorProduct.lid ℂ (LocalBanach s)).toLinearMap.comp
      (TensorProduct.map ((φ n).comp i).toLinearMap j.toLinearMap)
  have hD (n) (z : E ⊗[ℂ] F) :
      ‖D n z‖ ≤ ‖φ n‖ * injectiveTensorSeminorm V W z :=
    norm_localBanach_contraction_le E V W i j
      (fun x hx ↦ by rw [hi, localBanach_norm_coe]; exact hiV x hx)
      (fun y hy ↦ by rw [hj, localBanach_norm_coe]; exact hjW y hy) (φ n) z
  -- Transport the local series across the extended bilinear map on each pure tensor.
  have hs (z : E ⊗[ℂ] F) : HasSum (fun n ↦ c n • B (b n) (D n z)) (κ z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      have hs := (hseries (i x)).map (B.flip (j y)) (B.flip (j y)).continuous
      have heq : B (localBanachMap p q hq (i x)) (j y) = κ (x ⊗ₜ[ℂ] y) := by
        rw [hi, hj, localBanachMap_coe]
        let x' : WithLocalSeminorm q := x
        let y' : WithLocalSeminorm s := y
        change B₁.flip.fromCompletion (y' : LocalBanach s) (x' : LocalBanach q) = _
        rw [ContinuousLinearMap.fromCompletion_apply_coe, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.fromCompletion_apply_coe]
        rfl
      rw [← heq]
      refine hs.congr_fun fun n ↦ ?_
      simp [D, smul_smul, ContinuousLinearMap.flip_apply]
    | add z z' hz hz' => simpa only [map_add, smul_add] using hz.add hz'
  obtain ⟨A, hA⟩ := (show Tendsto (fun n ↦ ‖φ n‖) atTop (𝓝 0) by simpa using hφ.norm).bddAbove_range
  obtain ⟨M, hM⟩ := (show Tendsto (fun n ↦ ‖b n‖) atTop (𝓝 0) by simpa using hb.norm).bddAbove_range
  refine ⟨(∑' n, ‖c n‖) * (M * A), fun z ↦ ?_⟩
  have hAz : 0 ≤ A := (norm_nonneg (φ 0)).trans (hA (mem_range_self 0))
  have hMz : 0 ≤ M := (norm_nonneg (b 0)).trans (hM (mem_range_self 0))
  rw [← hκ, mul_assoc]
  apply (hs z).norm_le_of_bounded (hc.hasSum.mul_right _)
  intro n
  rw [norm_smul]
  calc
    _ ≤ ‖c n‖ * (‖b n‖ * ‖D n z‖) := by gcongr; exact hB _ _
    _ ≤ ‖c n‖ * (M * (A * injectiveTensorSeminorm V W z)) := by
      gcongr
      · exact hM (mem_range_self n)
      · exact (hD n z).trans (mul_le_mul_of_nonneg_right (hA (mem_range_self n)) (apply_nonneg _ _))
    _ = _ := by ring

omit [T2Space E] in
/-- Paper: Theorem C.2.4.2(2), p. 686. A generating projective seminorm is bounded
on pure tensors by the product of two continuous seminorms on the factors. -/
private theorem exists_projectiveSeminorm_pure_bound {F : Type*} [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] [PolynormableSpace ℂ F] (r : Seminorm ℂ (E ⊗[ℂ] F))
    (hr : ContinuousAt (fun v : E × F ↦ r (v.1 ⊗ₜ[ℂ] v.2)) 0) :
    ∃ (q : Seminorm ℂ E) (s : Seminorm ℂ F), Continuous q ∧ Continuous s ∧
      ∀ x y, r (x ⊗ₜ[ℂ] y) ≤ q x * s y := by
  have h : {v : E × F | r (v.1 ⊗ₜ[ℂ] v.2) < 1} ∈ 𝓝 0 :=
    hr.preimage_mem_nhds (show Iio (1 : ℝ) ∈ 𝓝 (r ((0 : E × F).1 ⊗ₜ[ℂ] (0 : E × F).2)) by
      simpa using Iio_mem_nhds one_pos)
  rw [show (0 : E × F) = ((0 : E), (0 : F)) from rfl, nhds_prod_eq] at h
  obtain ⟨U, hU, W, hW, hUW⟩ := Filter.mem_prod_iff.mp h
  obtain ⟨q, hq, hqU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hU
  obtain ⟨s, hs, hsW⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ F).mem_iff.mp hW
  refine ⟨q, s, hq, hs, fun x y ↦ ?_⟩
  have bound (a b : ℝ) (ha : q x < a) (hb : s y < b) :
      r (x ⊗ₜ[ℂ] y) ≤ a * b := by
    have ha₀ := (apply_nonneg q x).trans_lt ha
    have hb₀ := (apply_nonneg s y).trans_lt hb
    have hx : (a : ℂ)⁻¹ • x ∈ q.ball 0 1 := by
      rwa [Seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg ha₀.le, inv_mul_lt_iff₀ ha₀, mul_one]
    have hy : (b : ℂ)⁻¹ • y ∈ s.ball 0 1 := by
      rwa [Seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hb₀.le, inv_mul_lt_iff₀ hb₀, mul_one]
    have hlt : r (((a : ℂ)⁻¹ • x) ⊗ₜ[ℂ] ((b : ℂ)⁻¹ • y)) < 1 :=
      hUW (a := ((a : ℂ)⁻¹ • x, (b : ℂ)⁻¹ • y)) ⟨hqU hx, hsW hy⟩
    have hscaled := hlt.le
    rw [TensorProduct.smul_tmul_smul, map_smul_eq_mul, norm_mul, norm_inv, norm_inv,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha₀.le,
      Real.norm_of_nonneg hb₀.le,
      show a⁻¹ * b⁻¹ = (a * b)⁻¹ by simp [mul_inv_rev, mul_comm]] at hscaled
    rw [inv_mul_le_iff₀ (mul_pos ha₀ hb₀), mul_one] at hscaled
    exact hscaled
  have bound' (a : ℝ) (ha : q x < a) : r (x ⊗ₜ[ℂ] y) ≤ a * s y := by
    have ht : Tendsto (fun b : ℝ ↦ a * b) (𝓝[>] (s y)) (𝓝 (a * s y)) :=
      (continuous_const.mul continuous_id).continuousAt.mono_left inf_le_left
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin (a := s y) (s := Ioi (s y))] with b hb
    exact bound a b ha hb
  have ht : Tendsto (fun a : ℝ ↦ a * s y) (𝓝[>] (q x)) (𝓝 (q x * s y)) :=
    (continuous_id.mul continuous_const).continuousAt.mono_left inf_le_left
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin (a := q x) (s := Ioi (q x))] with a ha
  exact bound' a ha

omit [T2Space E] in
/-- Paper: Theorem C.2.4.2(2), p. 686. Local nuclear series imply continuity of
the identity from the injective topology to the projective topology. -/
private theorem continuous_injectiveTensor_to_projectiveTensor_of_localSeries
    (h : ∀ (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U),
      ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
        let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
        let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
        let T := localBanachMap p q (gauge_mono (absorbent_nhds_zero hV) hVU)
        ∃ (c : ℕ → ℂ) (φ : ℕ → LocalBanach p →L[ℂ] ℂ) (y : ℕ → LocalBanach q),
          Summable (fun n ↦ ‖c n‖) ∧ Tendsto φ atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
            ∀ x, HasSum (fun n ↦ (c n * φ n x) • y n) (T x))
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] :
    Continuous (show InjectiveTensor E F → ProjectiveTensor E F from id) := by
  let hI := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
      injectiveTensorSeminorm UV.1 UV.2)
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) // ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦
      p.val)
  refine hP.continuous_of_continuous_comp (LinearMap.id : InjectiveTensor E F →ₗ[ℂ] ProjectiveTensor E F)
    fun ⟨r, hr⟩ ↦ ?_
  obtain ⟨q, s, hq, hs, hrs⟩ := exists_projectiveSeminorm_pure_bound E r hr
  let U := q.ball 0 1
  let W : {W : Set F // W ∈ 𝓝 0} := ⟨s.ball 0 1, s.ball_mem_nhds hs one_pos⟩
  have hU : U ∈ 𝓝 0 := q.ball_mem_nhds hq one_pos
  obtain ⟨V, hV, bV, cV, hVU, c, φ, b, hc, hφ, hb, hseries⟩ :=
    h U hU (q.balanced_ball_zero 1) (q.convex_ball 0 1)
  let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
  have := PolynormableSpace.isTopologicalAddGroup (𝕜 := ℂ) (E := E)
  obtain ⟨i, hi⟩ := exists_localBanach_inclusion p (continuous_gauge cV hV)
  obtain ⟨j, hj⟩ := exists_localBanach_inclusion s hs
  have hqeq : gaugeSeminorm (q.balanced_ball_zero 1) (q.convex_ball 0 1)
      (absorbent_nhds_zero hU) = q :=
    DFunLike.coe_injective (q.restrictScalars ℝ).gauge_ball
  have hle := gauge_mono (absorbent_nhds_zero hV) hVU
  have hrs' : ∀ x y, r (x ⊗ₜ[ℂ] y) ≤
      gaugeSeminorm (q.balanced_ball_zero 1) (q.convex_ball 0 1) (absorbent_nhds_zero hU) x * s y := by
    rw [hqeq]
    exact hrs
  let V' : {V : Set E // V ∈ 𝓝 0} := ⟨V, hV⟩
  obtain ⟨C, hC⟩ := projectiveSeminorm_le_of_localBanach_series E hle V' W i j hi hj
    (fun x hx ↦ gauge_le_one_of_mem hx) (fun y hy ↦ (s.mem_ball_zero.mp hy).le)
    r hrs' c φ b hc hφ hb hseries
  let s' : Seminorm ℂ (InjectiveTensor E F) := injectiveTensorSeminorm V' W
  refine Seminorm.continuous_of_le (q := C.toNNReal • s') ?_ fun z ↦ (hC z).trans ?_
  · exact (hI.continuous_seminorm (V', W)).const_smul C.toNNReal
  · exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (apply_nonneg _ _)

/-- Paper: Theorem C.2.4.2(2), p. 686. An absolutely summing local Banach
comparison bounds sums of norms by the weak sums tested against the dual unit ball.
Deviation: This intermediate condition is used to derive the nuclear series. -/
def IsAbsolutelySummingLocalBanachMap {p q : Seminorm ℂ E} (h : q ≤ p) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : ℕ) (x : Fin n → LocalBanach p) (M : ℝ), 0 ≤ M →
      (∀ φ : LocalBanach p →L[ℂ] ℂ, ‖φ‖ ≤ 1 → ∑ i, ‖φ (x i)‖ ≤ M) →
      ∑ i, ‖localBanachMap p q h (x i)‖ ≤ C * M

omit [T2Space E] in
/-- Paper: Theorem C.2.4.2(2), p. 686. In a nuclear space, for each balanced convex
zero-neighborhood there is a smaller balanced convex zero-neighborhood whose local Banach space
maps to that of the original neighborhood with an absolute summability bound.

Deviation: This intermediate result establishes the absolute summability bound used to
derive the nuclear comparison map. -/
theorem exists_localBanachMap_absolutelySumming (h : IsNuclearTVS.{v, u} E)
    (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U) :
    ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
      let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
      let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
      IsAbsolutelySummingLocalBanachMap E
        (show q ≤ p from gauge_mono (absorbent_nhds_zero hV) hVU) := by
  classical
  have := PolynormableSpace.isTopologicalAddGroup (𝕜 := ℂ) (E := E)
  let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
  let F := ULift.{v} (LocalBanach q →L[ℂ] ℂ)
  have : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  obtain ⟨j, hj⟩ := exists_localBanach_inclusion q (continuous_gauge cU hU)
  let B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun x f ↦ f.down (j x))
    (by intros; simp) (by intros; simp) (by intros; rfl) (by intros; rfl)
  let r := (normSeminorm ℂ ℂ).comp (TensorProduct.lift B)
  have hr : ContinuousAt (fun z : E × F ↦ r (z.1 ⊗ₜ[ℂ] z.2)) 0 := by
    have hEval := (ContinuousLinearMap.apply ℂ (E' := LocalBanach q) ℂ).continuous₂
    exact (hEval.comp ((j.continuous.comp continuous_fst).prodMk
      (continuous_uliftDown.comp continuous_snd))).norm.continuousAt
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun r : {r : Seminorm ℂ (E ⊗[ℂ] F) //
      ContinuousAt (fun z : E × F ↦ r (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ r.val)
  let hI := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
      injectiveTensorSeminorm UV.1 UV.2)
  have hback : Continuous (show InjectiveTensor E F → ProjectiveTensor E F from id) := by
    let e := (h.2.2 F inferInstance inferInstance inferInstance inferInstance inferInstance).homeomorph
    refine e.continuous_symm.congr fun z ↦ ?_
    exact e.apply_symm_apply z
  obtain ⟨S, C, _, hC⟩ := Seminorm.bound_of_continuous hI r
    ((hP.continuous_seminorm ⟨r, hr⟩).comp hback)
  -- One pair of neighborhoods suffices by intersecting the finitely many pairs.
  let A := U ∩ ⋂ UV ∈ S, (UV.1.val : Set E)
  have hA : A ∈ 𝓝 0 := inter_mem hU (S.iInter_mem_sets.mpr fun UV _ ↦ UV.1.property)
  obtain ⟨p₀, hp₀, hV⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hA
  let V := p₀.ball 0 1
  have hV₀ : V ∈ 𝓝 0 := p₀.ball_mem_nhds hp₀ one_pos
  have bV : Balanced ℂ V := p₀.balanced_ball_zero 1
  have cV : Convex ℝ V := p₀.convex_ball 0 1
  have hVU : V ⊆ U := hV.trans inter_subset_left
  let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV₀)
  let T := localBanachMap p q (gauge_mono (absorbent_nhds_zero hV₀) hVU)
  let W : Set F := ⋂ UV ∈ S, (UV.2.val : Set F)
  have hW : W ∈ 𝓝 0 := S.iInter_mem_sets.mpr fun UV _ ↦ UV.2.property
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.mp hW
  let V' : {V : Set E // V ∈ 𝓝 0} := ⟨V, hV₀⟩
  let W' : {W : Set F // W ∈ 𝓝 0} := ⟨W, hW⟩
  have hVW (UV) (hUV : UV ∈ S) :
      injectiveTensorSeminorm UV.1 UV.2 ≤ injectiveTensorSeminorm V' W' := by
    intro z
    obtain ⟨hBdd, hSup⟩ := injectiveSeminorm_eq_ciSup V' W' z
    rw [(injectiveSeminorm_eq_ciSup UV.1 UV.2 z).2, hSup]
    have : Nonempty (StrongDual.polar ℂ UV.1.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    have : Nonempty (StrongDual.polar ℂ UV.2.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    apply ciSup_le
    rintro ⟨φ, ψ⟩
    have hφ : φ.val ∈ StrongDual.polar ℂ V :=
      (StrongDual.mem_polar_iff ℂ _).mpr fun x hx ↦
        (StrongDual.mem_polar_iff ℂ _).mp φ.property x
          (mem_iInter₂.mp (hV hx).2 UV hUV)
    have hψ : ψ.val ∈ StrongDual.polar ℂ W :=
      (StrongDual.mem_polar_iff ℂ _).mpr fun y hy ↦
        (StrongDual.mem_polar_iff ℂ _).mp ψ.property y (mem_iInter₂.mp hy UV hUV)
    exact le_ciSup hBdd (⟨φ.val, hφ⟩, ⟨ψ.val, hψ⟩)
  have hrVW (z : E ⊗[ℂ] F) : r z ≤ C * injectiveTensorSeminorm V' W' z :=
    (hC z).trans (mul_le_mul_of_nonneg_left ((Finset.sup_le hVW) z) C.coe_nonneg)
  have extend (φ : StrongDual.polar ℂ V) :
      ∃ g : LocalBanach p →L[ℂ] ℂ, ‖g‖ ≤ 1 ∧
        ∀ x : WithLocalSeminorm p, g (x : LocalBanach p) = φ.val x := by
    have bound (x : WithLocalSeminorm p) : ‖φ.val x‖ ≤ ‖x‖ := by
      change ‖φ.val x‖ ≤ gauge V x
      apply le_csInf (absorbent_nhds_zero hV₀).gauge_set_nonempty
      rintro a ⟨ha, y, hy, hxy⟩
      let x' : E := x
      change (a • y : E) = x' at hxy
      change ‖φ.val x'‖ ≤ a
      have hmap : φ.val (a • y) = a • φ.val y := φ.val.toLinearMap.map_smul_of_tower a y
      rw [← hxy, hmap, norm_smul, Real.norm_of_nonneg ha.le]
      exact mul_le_of_le_one_right ha.le ((StrongDual.mem_polar_iff ℂ _).mp φ.property y hy)
    let f := (show WithLocalSeminorm p →ₗ[ℂ] ℂ from φ.val.toLinearMap).mkContinuous 1
      (fun x ↦ (bound x).trans_eq (one_mul _).symm)
    refine ⟨f.fromCompletion, f.fromCompletion.opNorm_le_bound zero_le_one fun x ↦ ?_,
      fun x ↦ f.fromCompletion_apply_coe x⟩
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      rw [ContinuousLinearMap.fromCompletion_apply_coe, Completion.norm_coe, one_mul]
      exact bound x
  have bound (n : ℕ) (x : Fin n → WithLocalSeminorm p) (M : ℝ)
      (hMx : ∀ g : LocalBanach p →L[ℂ] ℂ, ‖g‖ ≤ 1 →
        ∑ i, ‖g (x i : LocalBanach p)‖ ≤ M) :
      ∑ i, ‖T (x i : LocalBanach p)‖ ≤ (C * (2 / δ)) * M := by
    -- Evaluate the tensor against norming functionals for the images of the given family.
    choose g hg hgx using fun i : Fin n ↦ exists_dual_vector'' ℂ (T (x i : LocalBanach p))
    let x' (i : Fin n) : E := x i
    let z : E ⊗[ℂ] F := ∑ i : Fin n, x' i ⊗ₜ[ℂ] (ULift.up (g i) : F)
    have hrz : r z = ∑ i, ‖T (x i : LocalBanach p)‖ := by
      change ‖TensorProduct.lift B z‖ = _
      have hterm (i : Fin n) :
          TensorProduct.lift B (x' i ⊗ₜ[ℂ] (ULift.up (g i) : F)) =
            (‖T (x i : LocalBanach p)‖ : ℂ) := by
        change g i (j (x' i)) = _
        have hji : j (x' i) = T (x i : LocalBanach p) :=
          (hj (x' i)).trans (localBanachMap_coe p q _ (x i)).symm
        exact (congrArg (g i) hji).trans (hgx i)
      rw [show TensorProduct.lift B z = ∑ i, (‖T (x i : LocalBanach p)‖ : ℂ) by
        exact (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ ↦ hterm i)]
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    have heps : injectiveTensorSeminorm V' W' z ≤ M * (2 / δ) := by
      rw [(injectiveSeminorm_eq_ciSup V' W' z).2]
      have : Nonempty (StrongDual.polar ℂ V'.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
      have : Nonempty (StrongDual.polar ℂ W'.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
      apply ciSup_le
      rintro ⟨φ, ψ⟩
      obtain ⟨f, hf, hfx⟩ := extend ⟨φ.val, φ.property⟩
      have hψ (i : Fin n) : ‖ψ.val (ULift.up (g i))‖ ≤ 2 / δ := by
        let a : ℂ := (δ / 2 : ℝ)
        have ha : ‖a‖ = δ / 2 := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hmem : a • (ULift.up (g i) : F) ∈ W :=
          hδW (by
            rw [Metric.mem_ball, dist_zero_right, norm_smul, ha, ULift.norm_up]
            nlinarith [hg i, mul_le_mul_of_nonneg_left (hg i) (show 0 ≤ δ / 2 by positivity)])
        have hnorm := (StrongDual.mem_polar_iff ℂ _).mp ψ.property _ hmem
        rw [map_smul, norm_smul, ha] at hnorm
        exact (le_div_iff₀ hδ).mpr (by nlinarith)
      change ‖tensorDualForm φ.val ψ.val z‖ ≤ _
      simp only [z, map_sum, tensorDualForm_tmul]
      refine (norm_sum_le _ _).trans ?_
      calc
        _ ≤ ∑ i, ‖f (x i : LocalBanach p)‖ * (2 / δ) := by
          apply Finset.sum_le_sum
          intro i _
          change ‖φ.val (x' i) * ψ.val (ULift.up (g i))‖ ≤ _
          rw [norm_mul, ← hfx (x i)]
          exact mul_le_mul_of_nonneg_left (hψ i) (norm_nonneg _)
        _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hMx f hf) (by positivity)
    rw [← hrz]
    exact (hrVW z).trans (by
      calc
        _ ≤ (C : ℝ) * (M * (2 / δ)) := mul_le_mul_of_nonneg_left heps C.coe_nonneg
        _ = _ := by ring)
  refine ⟨V, hV₀, bV, cV, hVU, (C : ℝ) * (2 / δ), by positivity, fun n x M _ hMx ↦ ?_⟩
  -- Pass the estimate to the completion using the sum of the approximation errors.
  have hd : DenseRange (fun ys : Fin n → WithLocalSeminorm p ↦ fun i ↦ (ys i : LocalBanach p)) :=
    DenseRange.piMap fun _ ↦ Completion.denseRange_coe
  have hclose : ∀ y : Fin n → LocalBanach p, ∑ i, ‖T (y i)‖ ≤
      ((C : ℝ) * (2 / δ)) * (M + ∑ i, ‖y i - x i‖) := by
    intro y
    refine hd.induction_on y ?_ (fun ys ↦ ?_)
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · refine bound n ys _ fun g hg ↦ ?_
      have hdiff (i : Fin n) :
          ‖g (ys i : LocalBanach p)‖ ≤ ‖g (x i)‖ + ‖(ys i : LocalBanach p) - x i‖ := by
        calc
          _ ≤ ‖g (x i)‖ + ‖g ((ys i : LocalBanach p) - x i)‖ := by
            rw [map_sub]
            calc
              _ = ‖g (x i) + (g (ys i : LocalBanach p) - g (x i))‖ := by
                rw [add_comm, sub_add_cancel]
              _ ≤ _ := norm_add_le _ _
          _ ≤ _ := add_le_add le_rfl ((g.le_opNorm _).trans
            (mul_le_of_le_one_left (norm_nonneg _) hg))
      exact (Finset.sum_le_sum fun i _ ↦ hdiff i).trans
        (by rw [Finset.sum_add_distrib]; exact add_le_add (hMx g hg) le_rfl)
  simpa using hclose x

omit [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E] in
/-- Paper: Theorem C.2.4.2(2), p. 686. Three successive absolutely summing local
Banach comparisons give the null-sequence series for their composite.
Pietsch factorization gives a 2-summing map into a Hilbert space followed by a
bounded map for each comparison. Composing adjacent factors gives two
Hilbert–Schmidt maps between Hilbert spaces. Their composite gives an absolutely
summable rank-one expansion, which can be rescaled to have norm-null factors. -/
theorem localBanachMap_hasSeries_of_three_absolutelySumming
    {p₀ p₁ p₂ p₃ : Seminorm ℂ E} (h₁ : p₀ ≤ p₁) (h₂ : p₁ ≤ p₂) (h₃ : p₂ ≤ p₃)
    (s₁ : IsAbsolutelySummingLocalBanachMap E h₁) (s₂ : IsAbsolutelySummingLocalBanachMap E h₂)
    (s₃ : IsAbsolutelySummingLocalBanachMap E h₃) :
    ∃ (c : ℕ → ℂ) (φ : ℕ → LocalBanach p₃ →L[ℂ] ℂ) (y : ℕ → LocalBanach p₀),
      Summable (fun n ↦ ‖c n‖) ∧ Tendsto φ atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
        ∀ x, HasSum (fun n ↦ (c n * φ n x) • y n) (localBanachMap p₃ p₀ (h₁.trans (h₂.trans h₃)) x) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hs⟩ := AbsolutelySumming.exists_series_comp_three
    (localBanachMap p₁ p₀ h₁) (localBanachMap p₂ p₁ h₂) (localBanachMap p₃ p₂ h₃) s₁ s₂ s₃
  refine ⟨c, φ, y, hc, hφ, hy, fun x ↦ ?_⟩
  have heq : localBanachMap p₁ p₀ h₁ (localBanachMap p₂ p₁ h₂ (localBanachMap p₃ p₂ h₃ x)) =
      localBanachMap p₃ p₀ (h₁.trans (h₂.trans h₃)) x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x =>
      rw [localBanachMap_coe p₃ p₂ h₃ x,
        localBanachMap_coe p₂ p₁ h₂ (show WithLocalSeminorm p₂ from x),
        localBanachMap_coe p₁ p₀ h₁ (show WithLocalSeminorm p₁ from x),
        localBanachMap_coe p₃ p₀ _ x]
  exact heq ▸ hs x

/-- Paper: Theorem C.2.4.2(2), p. 686. Nuclearity is equivalent to the existence,
inside each balanced convex zero-neighborhood, of another such neighborhood for
which the canonical local Banach space map is nuclear.
Deviation: Nuclearity of the Banach space map is expressed by the null-sequence
series characterization (C.2.4.2), with convergence at every input. -/
theorem isNuclearTVS_iff_localBanach_series :
    IsNuclearTVS.{v, u} E ↔
      ∀ (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U),
        ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
          let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
          let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
          let T := localBanachMap p q (gauge_mono (absorbent_nhds_zero hV) hVU)
          ∃ (c : ℕ → ℂ) (φ : ℕ → LocalBanach p →L[ℂ] ℂ) (y : ℕ → LocalBanach q),
            Summable (fun n ↦ ‖c n‖) ∧ Tendsto φ atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
              ∀ x, HasSum (fun n ↦ (c n * φ n x) • y n) (T x) := by
  constructor
  · intro h U hU bU cU
    obtain ⟨V₁, hV₁, bV₁, cV₁, h₁, s₁⟩ := exists_localBanachMap_absolutelySumming E h U hU bU cU
    obtain ⟨V₂, hV₂, bV₂, cV₂, h₂, s₂⟩ := exists_localBanachMap_absolutelySumming E h V₁ hV₁ bV₁ cV₁
    obtain ⟨V₃, hV₃, bV₃, cV₃, h₃, s₃⟩ := exists_localBanachMap_absolutelySumming E h V₂ hV₂ bV₂ cV₂
    exact ⟨V₃, hV₃, bV₃, cV₃, h₃.trans (h₂.trans h₁),
      localBanachMap_hasSeries_of_three_absolutelySumming E _ _ _ s₁ s₂ s₃⟩
  · intro h
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro F _ _ _ _ _
    let hI := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
        injectiveTensorSeminorm UV.1 UV.2)
    let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
        ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
    have hfwd : Continuous (show ProjectiveTensor E F → InjectiveTensor E F from id) :=
      hI.continuous_of_continuous_comp (LinearMap.id : ProjectiveTensor E F →ₗ[ℂ] InjectiveTensor E F)
        fun ⟨U, V⟩ ↦ hP.continuous_seminorm ⟨_, injectiveSeminorm_continuousAt_tmul U V⟩
    let e : ProjectiveTensor E F ≃ₜ InjectiveTensor E F :=
      ⟨Equiv.refl (E ⊗[ℂ] F), hfwd, continuous_injectiveTensor_to_projectiveTensor_of_localSeries E h F⟩
    exact e.isHomeomorph

omit [T2Space E] in
/-- The tensor comparison from the projective to the injective tensor product is
uniformly continuous. -/
theorem uniformContinuous_tensorComparison
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] :
    @UniformContinuous (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id := by
  let f : ProjectiveTensor E F →ₗ[ℂ] InjectiveTensor E F := LinearMap.id
  apply uniformContinuous_addMonoidHom_of_continuous (f := f)
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
      ContinuousAt (fun z : E × F ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
  exact (withGeneratingSeminorms_spec (E ⊗[ℂ] F) _).continuous_of_continuous_comp f
    fun ⟨U, V⟩ ↦ hP.continuous_seminorm
      ⟨_, injectiveSeminorm_continuousAt_tmul U V⟩

omit [T2Space E] in
/-- Paper: Definition C.2.4.1, p. 685. The tensor comparison is a homeomorphism
exactly when its map on completions is a homeomorphism. -/
private theorem isHomeomorph_completedTensorComparison_iff
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] :
    IsHomeomorph (@Completion.map (ProjectiveTensor E F) _ (InjectiveTensor E F) _ id) ↔
      @IsHomeomorph (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id := by
  have hforward := uniformContinuous_tensorComparison E F
  let g : InjectiveTensor E F →ₗ[ℂ] ProjectiveTensor E F := LinearMap.id
  constructor
  · intro h
    have hcomm : (@Completion.map (ProjectiveTensor E F) _ (InjectiveTensor E F) _ id) ∘
        (Completion.coe' : ProjectiveTensor E F → Completion (ProjectiveTensor E F)) =
        (fun z : ProjectiveTensor E F ↦
          (Completion.coe' : InjectiveTensor E F → Completion (InjectiveTensor E F)) z) := by
      funext z
      exact Completion.map_coe hforward z
    have hind := h.isInducing.comp Completion.isDenseInducing_coe.isInducing
    have hback : Continuous g := hind.continuous_iff.mpr (by
      rw [hcomm]
      exact @Completion.continuous_coe (InjectiveTensor E F) _)
    exact (⟨Equiv.refl (E ⊗[ℂ] F), hforward.continuous, hback⟩ :
      ProjectiveTensor E F ≃ₜ InjectiveTensor E F).isHomeomorph
  · intro h
    have hback : Continuous g := h.isInducing.continuous_iff.mpr
      (@continuous_id (InjectiveTensor E F) _)
    let e : ProjectiveTensor E F ≃ᵤ InjectiveTensor E F :=
      ⟨Equiv.refl (E ⊗[ℂ] F), hforward,
        uniformContinuous_addMonoidHom_of_continuous hback⟩
    exact (Completion.mapEquiv e).toHomeomorph.isHomeomorph

/-- Paper: Theorem C.2.4.2(3), p. 686. Each projective generator can be pulled back
from the projective tensor with the local Banach space of a continuous seminorm on
the second factor. If the comparison there is a homeomorphism, the generator is
continuous for the injective topology on the original tensor product. -/
private theorem continuous_projectiveSeminorm_of_localBanach
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [PolynormableSpace ℂ F] [T2Space F]
    (h : ∀ s : Seminorm ℂ F,
      @IsHomeomorph (ProjectiveTensor E (LocalBanach s)) (InjectiveTensor E (LocalBanach s)) _ _ id)
    (r : Seminorm ℂ (E ⊗[ℂ] F))
    (hr : ContinuousAt (fun z : E × F ↦ r (z.1 ⊗ₜ[ℂ] z.2)) 0) :
    @Continuous (InjectiveTensor E F) ℝ _ _ r := by
  obtain ⟨q, s, hq, hs, hbound⟩ := exists_projectiveSeminorm_pure_bound E r hr
  obtain ⟨j, hj⟩ := exists_localBanach_inclusion s hs
  let κ : E ⊗[ℂ] F →ₗ[ℂ] LocalBanach r := Completion.toComplL.toLinearMap.comp LinearMap.id
  have hκ (z : E ⊗[ℂ] F) : ‖κ z‖ = r z := localBanach_norm_coe r z
  -- Extend the pure-tensor map in the second factor, with values in the completion for r.
  let B₀ : WithLocalSeminorm q →L[ℂ] WithLocalSeminorm s →L[ℂ] LocalBanach r :=
    ((TensorProduct.mk ℂ E F).compr₂ κ :
      WithLocalSeminorm q →ₗ[ℂ] WithLocalSeminorm s →ₗ[ℂ] LocalBanach r).mkContinuous₂ 1
      (fun x y ↦ by
        change ‖κ (x ⊗ₜ[ℂ] y)‖ ≤ 1 * q x * s y
        rw [hκ, one_mul]
        exact hbound x y)
  let B := B₀.flip.fromCompletion
  have hcoe (x : E) (y : WithLocalSeminorm s) :
      B (y : LocalBanach s) x = κ (x ⊗ₜ[ℂ] y) := by
    change B₀.flip.fromCompletion (y : LocalBanach s) x = _
    rw [ContinuousLinearMap.fromCompletion_apply_coe]
    rfl
  have hB (x : E) (y : LocalBanach s) : ‖B y x‖ ≤ q x * ‖y‖ := by
    induction y using Completion.induction_on with
    | hp =>
      apply isClosed_le
      · exact ((ContinuousLinearMap.apply ℂ (LocalBanach r)
          (show WithLocalSeminorm q from x)).continuous.comp B.continuous).norm
      · exact continuous_const.mul continuous_norm
    | ih y =>
      rw [hcoe, hκ, localBanach_norm_coe s]
      exact hbound x y
  let L : E ⊗[ℂ] LocalBanach s →ₗ[ℂ] LocalBanach r :=
    TensorProduct.lift (LinearMap.mk₂ ℂ (fun x y ↦ B y x)
      (fun _ _ _ ↦ map_add _ _ _) (fun _ _ _ ↦ map_smul _ _ _)
      (fun _ _ _ ↦ by rw [map_add]; rfl) (fun _ _ _ ↦ by rw [map_smul]; rfl))
  let p := (normSeminorm ℂ (LocalBanach r)).comp L
  have hp : ContinuousAt (fun z : E × LocalBanach s ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0 := by
    have ht : Tendsto (fun z : E × LocalBanach s ↦ q z.1 * ‖z.2‖) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun z : E × LocalBanach s ↦ q z.1 * ‖z.2‖) :=
        (hq.comp continuous_fst).mul continuous_snd.norm
      simpa [ContinuousAt] using hcont.continuousAt (x := 0)
    have hzero : p ((0 : E) ⊗ₜ[ℂ] (0 : LocalBanach s)) = 0 := by simp
    change Tendsto _ _ (𝓝 (p ((0 : E) ⊗ₜ[ℂ] (0 : LocalBanach s))))
    rw [hzero]
    exact squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun z ↦ by
      change ‖L (z.1 ⊗ₜ[ℂ] z.2)‖ ≤ _
      rw [show L (z.1 ⊗ₜ[ℂ] z.2) = B z.2 z.1 from TensorProduct.lift.tmul _ _]
      exact hB z.1 z.2) ht
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] LocalBanach s)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] LocalBanach s) //
      ContinuousAt (fun z : E × LocalBanach s ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
  have hpP := hP.continuous_seminorm ⟨p, hp⟩
  have hpI : @Continuous (InjectiveTensor E (LocalBanach s)) ℝ _ _ p :=
    (h s).isQuotientMap.continuous_iff.mpr hpP
  have : PolynormableSpace ℂ (LocalBanach s) := (norm_withSeminorms ℂ _).toPolynormableSpace
  let T := injectiveTensorMap (ContinuousLinearMap.id ℂ E).toLinearMap j.toLinearMap
  have hL : L.comp T = κ := by
    apply TensorProduct.ext'
    intro x y
    change L (TensorProduct.map LinearMap.id j.toLinearMap (x ⊗ₜ[ℂ] y)) = κ (x ⊗ₜ[ℂ] y)
    rw [TensorProduct.map_tmul, TensorProduct.lift.tmul]
    change B (j y) x = κ (x ⊗ₜ[ℂ] y)
    rw [hj, hcoe]
  have heq : (fun z : InjectiveTensor E F ↦ p (T z)) = r := by
    funext z
    change ‖(L.comp T) z‖ = r z
    rw [hL]
    exact hκ z
  rw [← heq]
  exact hpI.comp (injectiveTensorMap_continuous (ContinuousLinearMap.id ℂ E) j)

/-- Paper: Theorem C.2.4.2(3), p. 686. Nuclearity can be tested on the completed
projective to injective comparison against Banach spaces. -/
theorem isNuclearTVS_iff_completedTensor_banach :
    IsNuclearTVS.{v, u} E ↔
      ∀ (F : Type (max v u)) (_ : NormedAddCommGroup F) (_ : NormedSpace ℂ F) (_ : CompleteSpace F),
        IsHomeomorph (@Completion.map (ProjectiveTensor E F) _ (InjectiveTensor E F) _ id) := by
  constructor
  · intro h F _ _ _
    have : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
    exact (isHomeomorph_completedTensorComparison_iff E F).mpr
      (h.2.2 F inferInstance inferInstance inferInstance inferInstance inferInstance)
  · intro h
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro F _ _ _ _ _
    have hlocal (s : Seminorm ℂ F) :
        @IsHomeomorph (ProjectiveTensor E (LocalBanach s)) (InjectiveTensor E (LocalBanach s)) _ _ id := by
      have : PolynormableSpace ℂ (LocalBanach s) := (norm_withSeminorms ℂ _).toPolynormableSpace
      exact (isHomeomorph_completedTensorComparison_iff E (LocalBanach s)).mp
        (h (LocalBanach s) inferInstance inferInstance inferInstance)
    let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
        ContinuousAt (fun z : E × F ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
    have hback : @Continuous (InjectiveTensor E F) (ProjectiveTensor E F) _ _ id :=
      hP.continuous_of_continuous_comp
        (LinearMap.id : InjectiveTensor E F →ₗ[ℂ] ProjectiveTensor E F)
        fun ⟨r, hr⟩ ↦ continuous_projectiveSeminorm_of_localBanach E hlocal r hr
    exact (⟨Equiv.refl (E ⊗[ℂ] F), (uniformContinuous_tensorComparison E F).continuous, hback⟩ :
      ProjectiveTensor E F ≃ₜ InjectiveTensor E F).isHomeomorph

/-- Paper: Theorem C.2.4.2(4), p. 686. Nuclearity is equivalent to the canonical
comparison on completed tensors being a homeomorphism against all Hausdorff locally
convex spaces. -/
theorem isNuclearTVS_iff_completedTensor :
    IsNuclearTVS.{v, u} E ↔
      ∀ (F : Type (max v u)) (_ : AddCommGroup F) (_ : Module ℂ F) (_ : TopologicalSpace F)
        (_ : PolynormableSpace ℂ F) (_ : T2Space F),
        IsHomeomorph (@Completion.map (ProjectiveTensor E F) _ (InjectiveTensor E F) _ id) := by
  constructor
  · rintro ⟨_, _, h⟩ F aF mF tF lcF hF
    let e : ProjectiveTensor E F ≃ InjectiveTensor E F :=
      ⟨id, id, fun _ ↦ rfl, fun _ ↦ rfl⟩
    have he := e.isHomeomorph_iff.mp (h F aF mF tF lcF hF)
    have hu : @UniformContinuous (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id :=
      uniformContinuous_addMonoidHom_of_continuous
        (α := ProjectiveTensor E F) (β := InjectiveTensor E F)
        (f := (LinearMap.id : ProjectiveTensor E F →ₗ[ℂ] InjectiveTensor E F)) he.1
    have hu' : @UniformContinuous (InjectiveTensor E F) (ProjectiveTensor E F) _ _ id :=
      uniformContinuous_addMonoidHom_of_continuous
        (α := InjectiveTensor E F) (β := ProjectiveTensor E F)
        (f := (LinearMap.id : InjectiveTensor E F →ₗ[ℂ] ProjectiveTensor E F)) he.2
    let eu : ProjectiveTensor E F ≃ᵤ InjectiveTensor E F := ⟨e, hu, hu'⟩
    exact (Completion.mapEquiv eu).toHomeomorph.isHomeomorph
  · intro h
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro F aF mF tF lcF hF
    have hc : @Continuous (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id := by
      let hI := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
        (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
          injectiveTensorSeminorm UV.1 UV.2)
      let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
        (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
          ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
      exact hI.continuous_of_continuous_comp
        (LinearMap.id : ProjectiveTensor E F →ₗ[ℂ] InjectiveTensor E F)
        fun ⟨U, V⟩ ↦ hP.continuous_seminorm ⟨_, injectiveSeminorm_continuousAt_tmul U V⟩
    have hu : @UniformContinuous (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id :=
      uniformContinuous_addMonoidHom_of_continuous
        (α := ProjectiveTensor E F) (β := InjectiveTensor E F)
        (f := (LinearMap.id : ProjectiveTensor E F →ₗ[ℂ] InjectiveTensor E F)) hc
    let coeP := Completion.coe' (α := ProjectiveTensor E F)
    let coeI := Completion.coe' (α := InjectiveTensor E F)
    let completedComparison := @Completion.map (ProjectiveTensor E F) _ (InjectiveTensor E F) _ id
    have hcoe : completedComparison ∘ coeP = coeI ∘ (id : ProjectiveTensor E F → InjectiveTensor E F) :=
      funext (Completion.map_coe (α := ProjectiveTensor E F) (β := InjectiveTensor E F) hu)
    have hi : IsInducing (completedComparison ∘ coeP) :=
      (h F aF mF tF lcF hF).isInducing.comp
        (Completion.isUniformInducing_coe (ProjectiveTensor E F)).isInducing
    rw [hcoe] at hi
    have hid : @IsInducing (ProjectiveTensor E F) (InjectiveTensor E F) _ _ id :=
      (Completion.isUniformInducing_coe (InjectiveTensor E F)).isInducing.of_comp_iff.mp hi
    exact isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨⟨hid, Function.injective_id⟩, Function.surjective_id⟩

end Characterizations

-- Remark C.2.4.3 (p. 686) records other authors' notation for the local Banach space.

section WeakDual

variable (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: Lemma C.2.4.4, p. 687. The local Banach space at a balanced convex
zero-neighborhood in the weak dual is finite-dimensional. -/
theorem finiteDimensional_weakDual_localBanach (U : Set (WeakDual ℂ E)) (hU : U ∈ 𝓝 0)
    (hb : Balanced ℂ U) (hc : Convex ℝ U) :
    FiniteDimensional ℂ (LocalBanach (gaugeSeminorm hb hc (absorbent_nhds_zero hU))) := by
  classical
  let p := gaugeSeminorm hb hc (absorbent_nhds_zero hU)
  let i : WeakDual ℂ E →ₗ[ℂ] LocalBanach p := Completion.toComplL.toLinearMap.comp LinearMap.id
  let evaluations := (topDualPairing ℂ E).toSeminormFamily
  change U ∈ 𝓝 (0 : WeakBilin (topDualPairing ℂ E)) at hU
  obtain ⟨⟨s, r⟩, hr, hsU⟩ :=
    (topDualPairing ℂ E).weakBilin_withSeminorms.hasBasis_zero_ball.mem_iff.mp hU
  let a : WeakDual ℂ E →ₗ[ℂ] (s → ℂ) :=
    LinearMap.pi fun x : s ↦ (topDualPairing ℂ E).flip (x : E)
  have hkerU : (a.ker : Set (WeakDual ℂ E)) ⊆ U := by
    intro φ hφ
    apply hsU
    change φ.toStrongDual ∈ (s.sup evaluations).ball 0 r
    rw [Seminorm.mem_ball_zero]
    refine Seminorm.finset_sup_apply_lt hr fun x hx ↦ ?_
    have hzero : φ x = 0 := congrFun (LinearMap.mem_ker.mp hφ) ⟨x, hx⟩
    change ‖φ x‖ < r
    simpa only [hzero, norm_zero] using hr
  -- Every positive dilate of U contains the kernel of the evaluation map.
  have hker : a.ker ≤ i.ker := by
    intro φ hφ
    let φ' : WithLocalSeminorm p := φ
    have hiφ : ‖i φ‖ = p φ := localBanach_norm_coe p φ'
    rw [LinearMap.mem_ker, ← norm_eq_zero, hiφ]
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) (apply_nonneg p φ)
    rw [zero_add]
    exact gauge_le_of_mem hε.le
      ⟨ε⁻¹ • φ, hkerU ((a.ker.restrictScalars ℝ).smul_mem ε⁻¹ hφ), smul_inv_smul₀ hε.ne' φ⟩
  have : FiniteDimensional ℂ (WeakDual ℂ E ⧸ a.ker) :=
    FiniteDimensional.of_injective a.quotKerEquivRange.toLinearMap a.quotKerEquivRange.injective
  have hker' : a.ker ≤ i.rangeRestrict.ker := by rwa [LinearMap.ker_rangeRestrict]
  have : FiniteDimensional ℂ i.range :=
    FiniteDimensional.of_surjective (a.ker.liftQ i.rangeRestrict hker') (by
      rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_rangeRestrict])
  -- The image in the completion is both dense and closed.
  have hdense : DenseRange i := Completion.denseRange_coe (α := WithLocalSeminorm p)
  apply FiniteDimensional.of_surjective i.range.subtype
  intro z
  have hz := hdense z
  rw [← LinearMap.coe_range, i.range.isClosed_of_finiteDimensional.closure_eq] at hz
  exact ⟨⟨z, hz⟩, rfl⟩

/-- Paper: Lemma C.2.4.4, p. 687. The weak dual of a Hausdorff locally convex space
is nuclear. -/
theorem isNuclearTVS_weakDual : IsNuclearTVS.{v, u} (WeakDual ℂ E) := by
  have : PolynormableSpace ℂ (WeakDual ℂ E) :=
    (topDualPairing ℂ E).weakBilin_withSeminorms.toPolynormableSpace
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro F _ _ _ _ _
  have hback : Continuous (show InjectiveTensor (WeakDual ℂ E) F →
      ProjectiveTensor (WeakDual ℂ E) F from id) := by
    refine continuous_injectiveTensor_to_projectiveTensor_of_localSeries (WeakDual ℂ E) ?_ F
    intro U hU bU cU
    refine ⟨U, hU, bU, cU, Subset.rfl, ?_⟩
    let p := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
    let T := localBanachMap p p le_rfl
    have : FiniteDimensional ℂ (LocalBanach p) := finiteDimensional_weakDual_localBanach E U hU bU cU
    -- Expand the comparison in a finite basis and extend the series by zero.
    let d := Module.finrank ℂ (LocalBanach p)
    let b := Module.finBasis ℂ (LocalBanach p)
    let c (n : ℕ) : ℂ := if n < d then 1 else 0
    let φ (n : ℕ) : LocalBanach p →L[ℂ] ℂ :=
      if h : n < d then (b.coord ⟨n, h⟩).toContinuousLinearMap else 0
    let y (n : ℕ) : LocalBanach p := if h : n < d then T (b ⟨n, h⟩) else 0
    refine ⟨c, φ, y, ?_, ?_, ?_, fun x ↦ ?_⟩
    · exact (hasSum_sum_of_ne_finset_zero (s := Finset.range d) fun n hn ↦ by
        simp only [Finset.mem_range] at hn
        simp [c, hn]).summable
    · exact tendsto_atTop_of_eventually_const (i₀ := d) fun _ hn ↦ dite_eq_right (not_lt.mpr hn)
    · exact tendsto_atTop_of_eventually_const (i₀ := d) fun _ hn ↦ dite_eq_right (not_lt.mpr hn)
    change LocalBanach p at x
    have hsum : (∑ n ∈ Finset.range d, (c n * φ n x) • y n) = T x := by
      rw [← Fin.sum_univ_eq_sum_range (fun n ↦ (c n * φ n x) • y n)]
      calc
        _ = ∑ i, T (b.repr x i • b i) := by
          exact Finset.sum_congr rfl fun i _ ↦ by simp [c, φ, y, i.isLt, Module.Basis.coord_apply]
        _ = T x := by rw [← map_sum, b.sum_repr]
    change HasSum (fun n ↦ (c n * φ n x) • y n) (T x)
    rw [← hsum]
    exact hasSum_sum_of_ne_finset_zero fun n hn ↦ by
      simp only [Finset.mem_range] at hn
      simp [c, hn]
  exact (⟨Equiv.refl (WeakDual ℂ E ⊗[ℂ] F), (uniformContinuous_tensorComparison _ F).continuous,
    hback⟩ : ProjectiveTensor (WeakDual ℂ E) F ≃ₜ InjectiveTensor (WeakDual ℂ E) F).isHomeomorph

end WeakDual

/-- Paper: Remark C.2.4.5, p. 687. Some Hausdorff locally convex spaces have a weak
dual that fails quasi-completeness. -/
theorem exists_weakDual_not_quasiComplete :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (_ : TopologicalSpace E)
      (_ : PolynormableSpace ℂ E) (_ : T2Space E),
      letI := IsTopologicalAddGroup.rightUniformSpace (WeakDual ℂ E)
      ¬ QuasiCompleteSpace ℂ (WeakDual ℂ E) := by
  classical
  let E := ℕ →₀ ℂ
  let coe : E →ₗ[ℂ] (ℕ → ℂ) := Finsupp.lcoeFun
  let : TopologicalSpace E := TopologicalSpace.induced coe inferInstance
  have hcoe : IsEmbedding coe := ⟨⟨rfl⟩, fun _ _ h ↦ Finsupp.ext (congrFun h)⟩
  have : PolynormableSpace ℂ E := PolynormableSpace.induced coe
  have : T2Space E := hcoe.t2Space
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  let := IsTopologicalAddGroup.rightUniformSpace (WeakDual ℂ E)
  let : IsUniformAddGroup (WeakDual ℂ E) := isUniformAddGroup_of_addCommGroup
  intro hq
  let coord (i : ℕ) : StrongDual ℂ E :=
    ⟨(LinearMap.proj i).comp coe, (continuous_apply i).comp hcoe.continuous⟩
  let partialSum (n : ℕ) : WeakDual ℂ E := StrongDual.toWeakDual (∑ i ∈ Finset.range n, coord i)
  have hpartial (n : ℕ) (x : E) : partialSum n x = ∑ i ∈ Finset.range n, x i := by
    change (∑ i ∈ Finset.range n, coord i) x = _
    rw [sum_apply]
    rfl
  -- The partial sums stabilize pointwise because each vector has finite support.
  let eval : WeakDual ℂ E →+ (E → ℂ) := ⟨⟨fun f x ↦ f x, rfl⟩, fun _ _ ↦ rfl⟩
  have heval : IsUniformInducing eval := AddMonoidHom.isUniformInducing_of_isInducing ⟨rfl⟩
  have hpoint (x : E) : Tendsto (fun n ↦ partialSum n x) atTop
      (𝓝 (x.sum fun _ z ↦ z)) := by
    obtain ⟨N, hN⟩ := x.support.exists_nat_subset_range
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn ↦ ?_
    rw [hpartial, Finsupp.sum]
    exact (Finset.sum_subset (hN.trans (Finset.range_mono hn))
      (fun i _ hi ↦ Finsupp.notMem_support_iff.mp hi)).symm
  have hc : CauchySeq partialSum := heval.cauchy_map_iff.mp (by
    rw [Filter.map_map]
    exact (tendsto_pi_nhds.mpr hpoint).cauchySeq)
  have hb := hc.totallyBounded_range.isVonNBounded ℂ
  obtain ⟨l, -, hl⟩ := cauchySeq_tendsto_of_isComplete
    (hq.quasiComplete hb.closure isClosed_closure) (fun n ↦ subset_closure (mem_range_self n)) hc
  -- The unit vectors tend to zero in the product topology, while the putative limit takes value 1.
  let e (n : ℕ) : E := Finsupp.single n 1
  have he : Tendsto e atTop (𝓝 0) := by
    apply hcoe.isInducing.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    refine tendsto_atTop_of_eventually_const (i₀ := i + 1) fun n hn ↦ ?_
    change Finsupp.single n (1 : ℂ) i = 0
    exact Finsupp.single_eq_of_ne (by omega)
  have hle (n : ℕ) : l (e n) = 1 := by
    calc
      l (e n) = (e n).sum (fun _ z ↦ z) :=
        tendsto_nhds_unique ((WeakDual.eval_continuous (e n)).tendsto l |>.comp hl)
          (hpoint (e n))
      _ = 1 := Finsupp.sum_single_index rfl
  have hz : Tendsto (fun n ↦ l (e n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, WeakDual.toStrongDual_apply, map_zero] using
      (l.toStrongDual.continuous.tendsto (0 : E)).comp he
  simp only [hle] at hz
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hz)

-- TODO(paper-gap): Footnote 15 leaves the argument for the particular strong dual
-- of a Fréchet space cited in Remark C.2.4.5 unfinished.

/-- Paper: Lemma C.2.4.6, p. 687. A point in the closed convex hull of a compact
set is represented on continuous functionals by a Radon probability measure on
that set.
Deviation: This states the scalar integral identity in the lemma. The vector-valued
Pettis assertion is deferred to §C.4. -/
theorem closedConvexHull_exists_radon_barycenter
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [T2Space E] (K : Set E) (hK : IsCompact K)
    {x : E} (hx : x ∈ closure (convexHull ℝ K)) :
    letI : MeasurableSpace K := borel K
    ∃ μ : Measure K, μ.Regular ∧ μ.InnerRegular ∧ μ univ = 1 ∧
      ∀ ℓ : StrongDual ℂ E,
        Integrable (fun y : K ↦ ℓ y.val) μ ∧ ℓ x = ∫ y : K, ℓ y.val ∂μ := by
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f (ℓ : StrongDual ℂ E) : BoundedContinuousFunction K ℂ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun y ↦ ℓ y.val, ℓ.continuous.comp continuous_subtype_val⟩
  let moments (p : ProbabilityMeasure K) (ℓ : StrongDual ℂ E) :=
    ∫ y, f ℓ y ∂(p : Measure K)
  have hmoments : Continuous moments := by
    apply continuous_pi
    intro ℓ
    rw [continuous_iff_continuousAt]
    intro p
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
      (tendsto_id (x := 𝓝 p)) (f ℓ)
  have hconvex : Convex ℝ (range moments) := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ a b ha hb hab
    let μ := ENNReal.ofReal a • (p : Measure K)
    let ν := ENNReal.ofReal b • (q : Measure K)
    let r : ProbabilityMeasure K := ⟨μ + ν, ⟨by
      simp [μ, ν, ← ENNReal.ofReal_add ha hb, hab]⟩⟩
    refine ⟨r, ?_⟩
    funext ℓ
    change ∫ y, f ℓ y ∂(μ + ν) = a • moments p ℓ + b • moments q ℓ
    rw [integral_add_measure
      (((f ℓ).integrable (μ := (p : Measure K))).smul_measure ENNReal.ofReal_ne_top)
      (((f ℓ).integrable (μ := (q : Measure K))).smul_measure ENNReal.ofReal_ne_top)]
    simp [moments, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
  let eval : E →ₗ[ℝ] (StrongDual ℂ E → ℂ) :=
    { toFun := fun z ℓ ↦ ℓ z
      map_add' := fun z w ↦ funext fun ℓ ↦ ℓ.map_add z w
      map_smul' := fun c z ↦ funext fun ℓ ↦ (ℓ.restrictScalars ℝ).map_smul c z }
  have heval : Continuous eval := continuous_pi fun ℓ ↦ ℓ.continuous
  -- The set of points represented by probability measures is closed and convex.
  have hclosed : IsClosed (eval ⁻¹' range moments) :=
    (isCompact_range hmoments).isClosed.preimage heval
  have hsubset : K ⊆ eval ⁻¹' range moments := by
    intro y hy
    refine ⟨⟨Measure.dirac ⟨y, hy⟩, Measure.dirac.isProbabilityMeasure⟩, ?_⟩
    funext ℓ
    exact integral_dirac (f ℓ) ⟨y, hy⟩
  obtain ⟨p, hp⟩ :=
    closure_minimal (convexHull_min hsubset (hconvex.linear_preimage eval)) hclosed hx
  -- Take a regular representative with the same integrals on continuous functions.
  obtain ⟨ν, hνreg, hνfin, hν⟩ := Measure.exists_regular_eq_of_compactSpace (p : Measure K)
  refine ⟨ν, hνreg, inferInstance, ?_, fun ℓ ↦ ?_⟩
  · apply (ENNReal.toReal_eq_one_iff _).mp
    simpa [measureReal_def] using (hν (1 : BoundedContinuousFunction K ℝ)).symm
  · have hpint := (f ℓ).integrable (μ := (p : Measure K))
    have hνint := (f ℓ).integrable (μ := ν)
    refine ⟨hνint, ?_⟩
    calc
      ℓ x = ∫ y, f ℓ y ∂(p : Measure K) := (congrFun hp ℓ).symm
      _ = ∫ y, f ℓ y ∂ν := by
        apply Complex.ext
        · let g := BoundedContinuousFunction.mkOfCompact
            ⟨fun y ↦ (f ℓ y).re, Complex.continuous_re.comp (f ℓ).continuous⟩
          exact (integral_re hpint).symm.trans ((hν g).trans (integral_re hνint))
        · let g := BoundedContinuousFunction.mkOfCompact
            ⟨fun y ↦ (f ℓ y).im, Complex.continuous_im.comp (f ℓ).continuous⟩
          exact (integral_im hpint).symm.trans ((hν g).trans (integral_im hνint))

/-- Paper: Remark C.2.4.7, p. 688. For a compact set in a Banach space whose span is
infinite-dimensional, the inverse to the point-evaluation embedding cannot extend
to a continuous linear map on the span of the evaluations. -/
theorem not_exists_continuousLinear_extension_evalInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : Set E) (hK : IsCompact K) (hKspan : ¬ FiniteDimensional ℂ (Submodule.span ℂ K)) :
    let δ : K → WeakDual ℂ C(K, ℂ) := fun y ↦
      StrongDual.toWeakDual (ContinuousMap.evalCLM ℂ y)
    let V := Submodule.span ℂ (range δ)
    ¬ ∃ T : V →L[ℂ] E, ∀ y : K, T ⟨δ y, Submodule.subset_span (mem_range_self y)⟩ = y.val := by
  classical
  intro δ V h
  obtain ⟨T, hT⟩ := h
  -- Continuity bounds the output norm by finitely many weak-dual evaluations.
  let pairing := topDualPairing ℂ C(K, ℂ)
  have hsub : IsInducing V.subtype := .subtypeVal
  obtain ⟨s, c, -, hbound⟩ := Seminorm.bound_comp_of_isInducing
    (p := (normSeminorm ℂ E).comp T.toLinearMap) T.continuous.norm
    pairing.weakBilin_withSeminorms hsub
  let a : V →ₗ[ℂ] (s → ℂ) :=
    LinearMap.pi fun f : s ↦ (pairing.flip (f : C(K, ℂ))).comp V.subtype
  have hker : a.ker ≤ T.toLinearMap.ker := by
    intro φ hφ
    have hsup : (s.sup pairing.toSeminormFamily) φ.val ≤ 0 := by
      refine Seminorm.finset_sup_apply_le le_rfl fun f hf ↦ ?_
      have hz : φ.val f = 0 := congrFun (LinearMap.mem_ker.mp hφ) ⟨f, hf⟩
      change ‖φ.val f‖ ≤ 0
      simp [hz]
    have hnorm : ‖T φ‖ ≤ (c : ℝ) * (s.sup pairing.toSeminormFamily) φ.val := hbound φ
    exact LinearMap.mem_ker.mpr (norm_le_zero_iff.mp
      (hnorm.trans (mul_nonpos_of_nonneg_of_nonpos c.coe_nonneg hsup)))
  have : FiniteDimensional ℂ (V ⧸ a.ker) :=
    FiniteDimensional.of_injective a.quotKerEquivRange.toLinearMap a.quotKerEquivRange.injective
  have : FiniteDimensional ℂ T.toLinearMap.range := by
    rw [← Submodule.range_liftQ a.ker T.toLinearMap hker]
    infer_instance
  apply hKspan
  refine Submodule.finiteDimensional_of_le (S₂ := T.toLinearMap.range) (Submodule.span_le.mpr ?_)
  intro y hy
  exact ⟨⟨δ ⟨y, hy⟩, Submodule.subset_span (mem_range_self _)⟩, hT ⟨y, hy⟩⟩

section IntegralForms

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Paper: Proposition C.2.4.8, p. 688. An integral bilinear form is the restriction
of a continuous linear functional on the injective tensor product to pure tensors. -/
def IsIntegralBilinearForm (b : E → F → ℂ) : Prop :=
  ∃ l : StrongDual ℂ (InjectiveTensor E F), ∀ x y, l (x ⊗ₜ[ℂ] y) = b x y

open scoped Pointwise in
/-- Paper: Proposition C.2.4.8, p. 688. A product of two continuous linear
functionals is an integral bilinear form.
Deviation: This is a check on the definition using a rank-one form. -/
theorem isIntegralBilinearForm_mul (φ : StrongDual ℂ E) (ψ : StrongDual ℂ F) :
    IsIntegralBilinearForm (fun x y ↦ φ x * ψ y) := by
  let p := (normSeminorm ℂ ℂ).comp φ.toLinearMap
  let q := (normSeminorm ℂ ℂ).comp ψ.toLinearMap
  let U : {U : Set E // U ∈ 𝓝 0} :=
    ⟨p.closedBall 0 1, Filter.mem_of_superset (p.ball_mem_nhds φ.continuous.norm one_pos)
      (p.ball_subset_closedBall _ _)⟩
  let V : {V : Set F // V ∈ 𝓝 0} :=
    ⟨q.closedBall 0 1, Filter.mem_of_superset (q.ball_mem_nhds ψ.continuous.norm one_pos)
      (q.ball_subset_closedBall _ _)⟩
  have hφ : φ ∈ StrongDual.polar ℂ U.val :=
    (StrongDual.mem_polar_iff ℂ _).mpr fun _ hx ↦ p.mem_closedBall_zero.mp hx
  have hψ : ψ ∈ StrongDual.polar ℂ V.val :=
    (StrongDual.mem_polar_iff ℂ _).mpr fun _ hy ↦ q.mem_closedBall_zero.mp hy
  let D := StrongDual.polar ℂ U.val × StrongDual.polar ℂ V.val
  let evaluation (f : D) := (normSeminorm ℂ ℂ).comp (tensorDualForm f.1.val f.2.val)
  -- Absorbency of the closed seminorm balls bounds all polar evaluations on each tensor.
  have hbound (z : E ⊗[ℂ] F) : ∃ C : ℝ, ∀ f : D, evaluation f z ≤ C := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        obtain ⟨a, x', hx', rfl⟩ : ∃ a : ℂ, x ∈ a • U.val := by
          simpa using (p.absorbent_closedBall_zero one_pos x).exists
        obtain ⟨b, y', hy', rfl⟩ : ∃ b : ℂ, y ∈ b • V.val := by
          simpa using (q.absorbent_closedBall_zero one_pos y).exists
        refine ⟨‖a‖ * ‖b‖, fun f ↦ ?_⟩
        have hx := (StrongDual.mem_polar_iff ℂ _).mp f.1.property x' hx'
        have hy := (StrongDual.mem_polar_iff ℂ _).mp f.2.property y' hy'
        change ‖tensorDualForm f.1.val f.2.val ((a • x') ⊗ₜ[ℂ] (b • y'))‖ ≤ _
        simp only [tensorDualForm_tmul, map_smul, norm_mul, norm_smul]
        simpa only [mul_one] using
          mul_le_mul (mul_le_of_le_one_right (norm_nonneg _) hx)
            (mul_le_of_le_one_right (norm_nonneg _) hy)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    | add z w hz hw =>
        obtain ⟨C, hC⟩ := hz
        obtain ⟨D', hD'⟩ := hw
        exact ⟨C + D', fun f ↦ (map_add_le_add (evaluation f) z w).trans
          (add_le_add (hC f) (hD' f))⟩
  have hb : BddAbove (range evaluation) := by
    apply Seminorm.bddAbove_range_iff.mpr
    intro z
    obtain ⟨C, hC⟩ := hbound z
    exact ⟨C, forall_mem_range.mpr hC⟩
  have hle : (normSeminorm ℂ ℂ).comp (tensorDualForm φ ψ) ≤ injectiveTensorSeminorm U V := by
    unfold injectiveTensorSeminorm
    rw [← ciSup_prod hb]
    exact le_ciSup hb (⟨φ, hφ⟩, ⟨ψ, hψ⟩)
  let T : InjectiveTensor E F →ₗ[ℂ] ℂ := tensorDualForm φ ψ
  have hT : Continuous T := by
    apply ((norm_withSeminorms ℂ ℂ).continuous_iff_continuous_comp T).mpr
    intro _
    exact Seminorm.continuous_of_le
      ((withGeneratingSeminorms_spec (E ⊗[ℂ] F) _).continuous_seminorm (U, V)) hle
  exact ⟨⟨T, hT⟩, tensorDualForm_tmul φ ψ⟩

open scoped Pointwise CompactlySupported

/-- Scalar multiplication in the first dual factor scales its tensor evaluation. -/
private theorem tensorDualForm_smul_left (a : ℂ) (φ : StrongDual ℂ E) (ψ : StrongDual ℂ F) :
    tensorDualForm (a • φ) ψ = a • tensorDualForm φ ψ := by
  apply TensorProduct.ext'
  intro x y
  simp [tensorDualForm_tmul, smul_eq_mul, mul_assoc]

/-- Tensor evaluation restricts to a continuous function on a product of weak-dual subsets. -/
private def tensorEvaluation (A : Set (WeakDual ℂ E)) (B : Set (WeakDual ℂ F)) :
    (E ⊗[ℂ] F) →ₗ[ℂ] C(A × B, ℂ) where
  toFun z := ⟨fun k ↦ tensorDualForm k.1.val.toStrongDual k.2.val.toStrongDual z, by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        simp only [tensorDualForm_tmul, WeakDual.toStrongDual_apply]
        exact ((WeakDual.eval_continuous x).comp (continuous_subtype_val.comp continuous_fst)).mul
          ((WeakDual.eval_continuous y).comp (continuous_subtype_val.comp continuous_snd))
    | add z w hz hw =>
        exact (hz.add hw).congr fun k ↦ (map_add (tensorDualForm _ _) z w).symm⟩
  map_add' z w := ContinuousMap.ext fun k ↦ map_add (tensorDualForm _ _) z w
  map_smul' a z := ContinuousMap.ext fun k ↦ map_smul (tensorDualForm _ _) a z

/-- Every equicontinuous family in the weak dual lies in the polar of a zero-neighborhood. -/
private theorem subset_polar_of_equicontinuousAt {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] {A : Set (WeakDual ℂ X)}
    (hA : EquicontinuousAt (fun φ : A ↦ (φ.val : X → ℂ)) 0) :
    ∃ U : {U : Set X // U ∈ 𝓝 0}, A ⊆ WeakDual.polar ℂ U.val := by
  have hU := Metric.equicontinuousAt_iff_right.mp hA 1 one_pos
  refine ⟨⟨_, hU⟩, fun φ hφ x hx ↦ ?_⟩
  have h := hx (⟨φ, hφ⟩ : A)
  change ‖φ x‖ ≤ 1
  simpa only [map_zero, dist_zero_left] using h.le

/-- The weak-dual polar of a zero-neighborhood is equicontinuous at zero. -/
private theorem equicontinuousAt_weakDual_polar {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [ContinuousConstSMul ℂ X] {U : Set X} (hU : U ∈ 𝓝 0) :
    EquicontinuousAt (fun φ : WeakDual.polar ℂ U ↦ (φ.val : X → ℂ)) 0 := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨a, ha, haε⟩ := NormedField.exists_norm_lt ℂ hε
  have hnear : a • U ∈ 𝓝 (0 : X) := by
    simpa using smul_mem_nhds_smul₀ (norm_pos_iff.mp ha) hU
  filter_upwards [hnear] with x hx φ
  obtain ⟨y, hy, rfl⟩ := hx
  change dist (φ.val 0) (φ.val (a • y)) < ε
  rw [map_zero, dist_zero_left, map_smul, norm_smul]
  exact (mul_le_of_le_one_right ha.le (φ.property y hy)).trans_lt haε

/-- Shrinking the two zero-neighborhoods combines finitely many injective seminorm
bounds and absorbs the constant into the first polar. -/
private theorem exists_injectiveTensorSeminorm_bound [PolynormableSpace ℂ E]
    [PolynormableSpace ℂ F] (l : StrongDual ℂ (InjectiveTensor E F)) :
    ∃ (U : {U : Set E // U ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0}),
      ∀ z, ‖l z‖ ≤ injectiveTensorSeminorm U V z := by
  let p (UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0}) :
      Seminorm ℂ (E ⊗[ℂ] F) := injectiveTensorSeminorm UV.1 UV.2
  let q := (normSeminorm ℂ ℂ).comp l.toLinearMap
  obtain ⟨S, C, -, hC⟩ := Seminorm.bound_of_continuous
    (withGeneratingSeminorms_spec (E ⊗[ℂ] F) p) q l.continuous.norm
  let U : {U : Set E // U ∈ 𝓝 0} :=
    ⟨⋂ UV ∈ S, UV.1.val, S.iInter_mem_sets.mpr fun UV _ ↦ UV.1.property⟩
  let V : {V : Set F // V ∈ 𝓝 0} :=
    ⟨⋂ UV ∈ S, UV.2.val, S.iInter_mem_sets.mpr fun UV _ ↦ UV.2.property⟩
  let d : ℂ := (max 1 (C : ℝ) : ℝ)
  have hd : ‖d‖ = max 1 (C : ℝ) := Complex.norm_of_nonneg (by positivity)
  have hdpos : 0 < ‖d‖ := by rw [hd]; exact zero_lt_one.trans_le (le_max_left _ _)
  have hdne : d ≠ 0 := norm_pos_iff.mp hdpos
  let W : {W : Set E // W ∈ 𝓝 0} :=
    ⟨d⁻¹ • U.val, by simpa using smul_mem_nhds_smul₀ (inv_ne_zero hdne) U.property⟩
  refine ⟨W, V, fun z ↦ (hC z).trans ?_⟩
  change E ⊗[ℂ] F at z
  have hW := injectiveSeminorm_eq_ciSup W V z
  have hS : (S.sup p) z ≤ injectiveTensorSeminorm W V z / ‖d‖ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun UV hUV ↦ ?_
    have : Nonempty (StrongDual.polar ℂ UV.1.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    have : Nonempty (StrongDual.polar ℂ UV.2.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    change injectiveTensorSeminorm UV.1 UV.2 z ≤ _
    rw [(injectiveSeminorm_eq_ciSup UV.1 UV.2 z).2]
    apply ciSup_le
    rintro ⟨φ, ψ⟩
    have hφ : d • φ.val ∈ StrongDual.polar ℂ W.val := by
      rintro _ ⟨x, hx, rfl⟩
      change ‖d * φ.val (d⁻¹ • x)‖ ≤ 1
      rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hdne, one_mul]
      exact φ.property x (mem_iInter₂.mp hx UV hUV)
    have hψ : ψ.val ∈ StrongDual.polar ℂ V.val :=
      fun y hy ↦ ψ.property y (mem_iInter₂.mp hy UV hUV)
    have hz := le_ciSup hW.1 (⟨d • φ.val, hφ⟩, ⟨ψ.val, hψ⟩)
    rw [← hW.2] at hz
    change ‖tensorDualForm (d • φ.val) ψ.val z‖ ≤ _ at hz
    rw [tensorDualForm_smul_left, LinearMap.smul_apply, norm_smul] at hz
    exact (le_div_iff₀ hdpos).mpr (by rwa [mul_comm])
  change (C : ℝ) * (S.sup p) z ≤ _
  calc
    _ ≤ ‖d‖ * (S.sup p) z := mul_le_mul_of_nonneg_right
      (hd ▸ le_max_right _ _) (apply_nonneg _ _)
    _ ≤ _ := by rwa [mul_comm, ← le_div_iff₀ hdpos]

/-- Rotating the first functional in a polar makes the real part of an evaluation
as large as its complex modulus. -/
private theorem injectiveTensorSeminorm_le_iSup_re [PolynormableSpace ℂ E]
    [PolynormableSpace ℂ F] (U : {U : Set E // U ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0})
    (z : E ⊗[ℂ] F)
    (hK : CompactSpace (WeakDual.polar ℂ U.val × WeakDual.polar ℂ V.val)) :
    injectiveTensorSeminorm U V z ≤
      ⨆ k, (tensorEvaluation (WeakDual.polar ℂ U.val) (WeakDual.polar ℂ V.val) z k).re := by
  let e := tensorEvaluation (WeakDual.polar ℂ U.val) (WeakDual.polar ℂ V.val) z
  have hbdd : BddAbove (range fun k ↦ (e k).re) :=
    (isCompact_range (Complex.continuous_re.comp e.continuous)).bddAbove
  have : Nonempty (StrongDual.polar ℂ U.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  have : Nonempty (StrongDual.polar ℂ V.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  rw [(injectiveSeminorm_eq_ciSup U V z).2]
  apply ciSup_le
  rintro ⟨φ, ψ⟩
  let w := tensorDualForm φ.val ψ.val z
  by_cases hw : w = 0
  · have h := le_ciSup hbdd (⟨φ.val.toWeakDual, φ.property⟩, ⟨ψ.val.toWeakDual, ψ.property⟩)
    change w.re ≤ _ at h
    change ‖w‖ ≤ _
    simpa [hw] using h
  · let a : ℂ := (‖w‖ : ℂ) / w
    have ha : ‖a‖ = 1 := by
      rw [norm_div, Complex.norm_of_nonneg (norm_nonneg w), div_self (norm_ne_zero_iff.mpr hw)]
    have hφ : (a • φ.val).toWeakDual ∈ WeakDual.polar ℂ U.val := by
      intro x hx
      change ‖a • φ.val x‖ ≤ 1
      rw [norm_smul, ha, one_mul]
      exact φ.property x hx
    have h := le_ciSup hbdd (⟨(a • φ.val).toWeakDual, hφ⟩, ⟨ψ.val.toWeakDual, ψ.property⟩)
    change (tensorDualForm (a • φ.val) ψ.val z).re ≤ _ at h
    rw [tensorDualForm_smul_left, LinearMap.smul_apply, smul_eq_mul, show
      a * tensorDualForm φ.val ψ.val z = (‖w‖ : ℂ) from div_mul_cancel₀ _ hw, Complex.ofReal_re] at h
    exact h

/-- Paper: Proposition C.2.4.8, p. 688. A continuous bilinear form is integral
exactly when a positive Radon measure of mass at most one on a product of weakly
closed equicontinuous sets represents it by integrating products of evaluations. -/
theorem isIntegralBilinearForm_iff_radon
    [PolynormableSpace ℂ E] [T2Space E] [PolynormableSpace ℂ F] [T2Space F]
    (b : E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (hb : Continuous (fun z : E × F ↦ b z.1 z.2)) :
    IsIntegralBilinearForm (fun x y ↦ b x y) ↔
      ∃ (A : Set (WeakDual ℂ E)) (B : Set (WeakDual ℂ F)),
        IsClosed A ∧ IsClosed B ∧ IsCompact A ∧ IsCompact B ∧
        EquicontinuousAt (fun φ : A ↦ (φ.val : E → ℂ)) 0 ∧
        EquicontinuousAt (fun ψ : B ↦ (ψ.val : F → ℂ)) 0 ∧
        letI : MeasurableSpace (A × B) := borel (A × B)
        ∃ μ : Measure (A × B), μ.Regular ∧ μ.InnerRegular ∧ μ univ ≤ 1 ∧
          ∀ x y, Integrable (fun z : A × B ↦ z.1.val x * z.2.val y) μ ∧
            b x y = ∫ z : A × B, z.1.val x * z.2.val y ∂μ := by
  clear hb
  classical
  have := PolynormableSpace.isTopologicalAddGroup (𝕜 := ℂ) (E := E)
  have := PolynormableSpace.isTopologicalAddGroup (𝕜 := ℂ) (E := F)
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨U, V, hbound⟩ := exists_injectiveTensorSeminorm_bound l
    let A := WeakDual.polar ℂ U.val
    let B := WeakDual.polar ℂ V.val
    have hA : IsCompact A := isCompact_weakDual_polar U.property
    have hB : IsCompact B := isCompact_weakDual_polar V.property
    refine ⟨A, B, WeakDual.isClosed_polar _ _, WeakDual.isClosed_polar _ _, hA, hB,
      equicontinuousAt_weakDual_polar U.property, equicontinuousAt_weakDual_polar V.property, ?_⟩
    let : CompactSpace A := isCompact_iff_compactSpace.mp hA
    let : CompactSpace B := isCompact_iff_compactSpace.mp hB
    have : Nonempty A := ⟨⟨0, fun x hx ↦ by simp⟩⟩
    have : Nonempty B := ⟨⟨0, fun x hx ↦ by simp⟩⟩
    let : MeasurableSpace (A × B) := borel (A × B)
    let : BorelSpace (A × B) := ⟨rfl⟩
    let : Module ℝ (E ⊗[ℂ] F) := Module.compHom _ (algebraMap ℝ ℂ)
    let : IsScalarTower ℝ ℂ (E ⊗[ℂ] F) := IsScalarTower.of_compHom ℝ ℂ _
    let e := tensorEvaluation A B
    -- Domination by the supremum of real evaluations gives a positive extension.
    let J : (E ⊗[ℂ] F) →ₗ[ℝ] C_c(A × B, ℝ) :=
      { toFun z := ⟨⟨fun k ↦ (e z k).re, Complex.continuous_re.comp (e z).continuous⟩,
          HasCompactSupport.of_compactSpace _⟩
        map_add' z w := CompactlySupportedContinuousMap.ext fun k ↦ by
          change (e (z + w) k).re = (e z k).re + (e w k).re
          rw [map_add, ContinuousMap.add_apply, Complex.add_re]
        map_smul' r z := CompactlySupportedContinuousMap.ext fun k ↦ by
          change (e ((r : ℂ) • z) k).re = r * (e z k).re
          rw [map_smul, ContinuousMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul] }
    let L : (E ⊗[ℂ] F) →ₗ[ℝ] ℝ := Complex.reLm.comp (l.toLinearMap.restrictScalars ℝ)
    have hL (z : E ⊗[ℂ] F) : L z ≤ ⨆ k, J z k :=
      (Complex.re_le_norm _).trans ((hbound z).trans
        (injectiveTensorSeminorm_le_iSup_re U V z inferInstance))
    obtain ⟨μ, hμreg, hμinner, hμmass, hμ⟩ := exists_radon_of_le_iSup J L hL
    have : IsFiniteMeasure μ := ⟨hμmass.trans_lt ENNReal.one_lt_top⟩
    have hint (z : E ⊗[ℂ] F) : Integrable (e z) μ :=
      (BoundedContinuousFunction.mkOfCompact (e z)).integrable (μ := μ)
    have hre (z : E ⊗[ℂ] F) : (l z).re = (∫ k, e z k ∂μ).re :=
      (hμ z).trans (integral_re (hint z))
    refine ⟨μ, hμreg, hμinner, hμmass, fun x y ↦ ?_⟩
    have hEval (k : A × B) : e (x ⊗ₜ[ℂ] y) k = k.1.val x * k.2.val y := tensorDualForm_tmul _ _ _ _
    simp_rw [← hEval]
    refine ⟨hint _, ?_⟩
    rw [← (show l (x ⊗ₜ[ℂ] y) = b x y from hl x y)]
    apply Complex.ext (hre _)
    -- Recover the imaginary part from the real identity at the rotated tensor.
    let z : E ⊗[ℂ] F := x ⊗ₜ[ℂ] y
    have hlI : l (Complex.I • z) = Complex.I * l z := l.map_smul _ _
    have heI : (∫ k, e (Complex.I • z) k ∂μ) = Complex.I * ∫ k, e z k ∂μ := by
      simp only [map_smul, ContinuousMap.smul_apply, smul_eq_mul]
      exact integral_const_mul _ _
    have hi := hre (Complex.I • z)
    rwa [hlI, heI, Complex.I_mul_re, Complex.I_mul_re, neg_inj] at hi
  · rintro ⟨A, B, -, -, hA, hB, hAeq, hBeq, μ, -, -, hμmass, hμ⟩
    obtain ⟨U, hU⟩ := subset_polar_of_equicontinuousAt hAeq
    obtain ⟨V, hV⟩ := subset_polar_of_equicontinuousAt hBeq
    let : CompactSpace A := isCompact_iff_compactSpace.mp hA
    let : CompactSpace B := isCompact_iff_compactSpace.mp hB
    let : MeasurableSpace (A × B) := borel (A × B)
    let : BorelSpace (A × B) := ⟨rfl⟩
    have : IsFiniteMeasure μ := ⟨hμmass.trans_lt ENNReal.one_lt_top⟩
    let e := tensorEvaluation A B
    have hint (z : E ⊗[ℂ] F) : Integrable (e z) μ :=
      (BoundedContinuousFunction.mkOfCompact (e z)).integrable (μ := μ)
    let l : (E ⊗[ℂ] F) →ₗ[ℂ] ℂ :=
      { toFun z := ∫ k, e z k ∂μ
        map_add' z w := by
          simp only [map_add, ContinuousMap.add_apply]
          exact integral_add (hint z) (hint w)
        map_smul' a z := by simp only [map_smul, ContinuousMap.smul_apply, integral_smul, RingHom.id_apply] }
    have hbound (z : E ⊗[ℂ] F) : ‖l z‖ ≤ injectiveTensorSeminorm U V z := by
      obtain ⟨hBdd, hSup⟩ := injectiveSeminorm_eq_ciSup U V z
      have hpoint (k : A × B) : ‖e z k‖ ≤ injectiveTensorSeminorm U V z := by
        rw [hSup]
        exact le_ciSup hBdd
          (⟨k.1.val.toStrongDual, hU k.1.property⟩, ⟨k.2.val.toStrongDual, hV k.2.property⟩)
      have hmass : μ.real univ ≤ 1 := by
        simpa only [measureReal_def, ENNReal.toReal_one] using
          (ENNReal.toReal_mono ENNReal.one_ne_top hμmass)
      exact (norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hpoint)).trans
        (mul_le_of_le_one_right (apply_nonneg _ _) hmass)
    let hI := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
        injectiveTensorSeminorm UV.1 UV.2)
    have hc : Continuous (show InjectiveTensor E F →ₗ[ℂ] ℂ from l) :=
      hI.continuous_normedSpace_rng ℂ l ⟨{(U, V)}, 1, by
        rw [one_smul]
        change (normSeminorm ℂ ℂ).comp l ≤ ({(U, V)} : Finset _).sup
          (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
            injectiveTensorSeminorm UV.1 UV.2)
        rw [Finset.sup_singleton]
        exact hbound⟩
    refine ⟨⟨l, hc⟩, fun x y ↦ ?_⟩
    change (∫ k : A × B, e (x ⊗ₜ[ℂ] y) k ∂μ) = b x y
    have hEval (k : A × B) : e (x ⊗ₜ[ℂ] y) k = k.1.val x * k.2.val y := tensorDualForm_tmul _ _ _ _
    simpa only [hEval] using (hμ x y).2.symm

end IntegralForms

section IntegralComparisons

open scoped NNReal

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
  [PolynormableSpace ℂ X] [PolynormableSpace ℂ Y]

/-- A seminorm continuous for the injective topology is bounded by one injective
generator whose first neighborhood lies in a prescribed zero-neighborhood. -/
private theorem exists_injectiveSeminorm_bound
    (U₀ : Set X) (hU₀ : U₀ ∈ 𝓝 0) (r : Seminorm ℂ (InjectiveTensor X Y))
    (hr : Continuous r) :
    ∃ (U : {U : Set X // U ∈ 𝓝 0}) (V : {V : Set Y // V ∈ 𝓝 0}) (C : ℝ≥0),
      U.val ⊆ U₀ ∧ ∀ z, r z ≤ C * injectiveTensorSeminorm U V z := by
  classical
  let P (UV : {U : Set X // U ∈ 𝓝 0} × {V : Set Y // V ∈ 𝓝 0}) :=
    injectiveTensorSeminorm UV.1 UV.2
  obtain ⟨S, C, _, hC⟩ := Seminorm.bound_of_continuous (withGeneratingSeminorms_spec _ P) r hr
  let U : {U : Set X // U ∈ 𝓝 0} :=
    ⟨U₀ ∩ ⋂ UV ∈ S, UV.1.val, inter_mem hU₀ (S.iInter_mem_sets.mpr fun UV _ ↦ UV.1.property)⟩
  let V : {V : Set Y // V ∈ 𝓝 0} :=
    ⟨⋂ UV ∈ S, UV.2.val, S.iInter_mem_sets.mpr fun UV _ ↦ UV.2.property⟩
  have hsup : S.sup P ≤ injectiveTensorSeminorm U V := by
    refine Finset.sup_le fun UV hUV w ↦ ?_
    have hU : U.val ⊆ UV.1.val := fun _ hx ↦ mem_iInter₂.mp hx.2 UV hUV
    have hV : V.val ⊆ UV.2.val := fun _ hy ↦ mem_iInter₂.mp hy UV hUV
    obtain ⟨hBdd, hSup⟩ := injectiveSeminorm_eq_ciSup U V w
    rw [(injectiveSeminorm_eq_ciSup UV.1 UV.2 w).2, hSup]
    have : Nonempty (StrongDual.polar ℂ UV.1.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    have : Nonempty (StrongDual.polar ℂ UV.2.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    apply ciSup_le
    rintro ⟨φ, ψ⟩
    have hφ : φ.val ∈ StrongDual.polar ℂ U.val :=
      (topDualPairing ℂ X).flip.polar_antitone hU φ.property
    have hψ : ψ.val ∈ StrongDual.polar ℂ V.val :=
      (topDualPairing ℂ Y).flip.polar_antitone hV ψ.property
    exact le_ciSup hBdd (⟨φ.val, hφ⟩, ⟨ψ.val, hψ⟩)
  exact ⟨U, V, C, inter_subset_left, fun z ↦
    (hC z).trans (mul_le_mul_of_nonneg_left (hsup z) C.coe_nonneg)⟩

/-- Two functionals bounded on the chosen neighborhoods give a tensor evaluation
bounded by the corresponding injective seminorm times the product of their bounds. -/
private theorem norm_tensorDualForm_le_mul_injectiveSeminorm
    (U : {U : Set X // U ∈ 𝓝 0}) (V : {V : Set Y // V ∈ 𝓝 0})
    (φ : StrongDual ℂ X) (ψ : StrongDual ℂ Y) (z : X ⊗[ℂ] Y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hφ : ∀ x ∈ U.val, ‖φ x‖ ≤ a) (hψ : ∀ y ∈ V.val, ‖ψ y‖ ≤ b) :
    ‖tensorDualForm φ ψ z‖ ≤ (a * b) * injectiveTensorSeminorm U V z := by
  let φ' := (a : ℂ)⁻¹ • φ
  let ψ' := (b : ℂ)⁻¹ • ψ
  have hpφ : φ' ∈ StrongDual.polar ℂ U.val :=
    (StrongDual.mem_polar_iff ℂ _).mpr fun x hx ↦ by
      rw [smul_apply, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg ha.le, inv_mul_le_iff₀ ha, mul_one]
      exact hφ x hx
  have hpψ : ψ' ∈ StrongDual.polar ℂ V.val :=
    (StrongDual.mem_polar_iff ℂ _).mpr fun y hy ↦ by
      rw [smul_apply, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hb.le, inv_mul_le_iff₀ hb, mul_one]
      exact hψ y hy
  have hφ' : (a : ℂ) • φ' = φ := smul_inv_smul₀ (by exact_mod_cast ha.ne') _
  have hψ' : (b : ℂ) • ψ' = ψ := smul_inv_smul₀ (by exact_mod_cast hb.ne') _
  have heq : tensorDualForm φ ψ = ((a * b : ℝ) : ℂ) • tensorDualForm φ' ψ' := by
    apply TensorProduct.ext'
    intro x y
    rw [← hφ', ← hψ']
    simp only [tensorDualForm_tmul, LinearMap.smul_apply, smul_apply,
      smul_eq_mul, Complex.ofReal_mul]
    ring
  rw [heq, LinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  obtain ⟨hBdd, hSup⟩ := injectiveSeminorm_eq_ciSup U V z
  rw [hSup]
  exact mul_le_mul_of_nonneg_left (le_ciSup hBdd (⟨φ', hpφ⟩, ⟨ψ', hpψ⟩)) (by positivity)

/-- Paper: Theorem C.2.4.9, p. 688. An integral local comparison bounds a
projective generator by an injective generator. Test the projective generator
against a norming functional on its seminorm completion. -/
private theorem projectiveSeminorm_le_of_localBanach_integral
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [PolynormableSpace ℂ F] {p q : Seminorm ℂ E} {s : Seminorm ℂ F} (hq : q ≤ p)
    (V : {V : Set E // V ∈ 𝓝 0}) (W : {W : Set F // W ∈ 𝓝 0})
    (i : E →L[ℂ] LocalBanach p) (j : F →L[ℂ] LocalBanach s)
    (hi : ∀ x : E, i x = (show WithLocalSeminorm p from x))
    (hj : ∀ y : F, j y = (show WithLocalSeminorm s from y))
    (hiV : ∀ x ∈ V.val, p x ≤ 1) (hjW : ∀ y ∈ W.val, s y ≤ 1)
    (r : Seminorm ℂ (E ⊗[ℂ] F)) (hr : ∀ x y, r (x ⊗ₜ[ℂ] y) ≤ q x * s y)
    (hT : IsIntegralBilinearForm (fun (x : LocalBanach p) (φ : StrongDual ℂ (LocalBanach q)) ↦
      φ (localBanachMap p q hq x))) :
    ∃ C : ℝ≥0, ∀ z, r z ≤ C * injectiveTensorSeminorm V W z := by
  let X := LocalBanach p
  let Y := StrongDual ℂ (LocalBanach q)
  obtain ⟨l, hl⟩ := hT
  let : PolynormableSpace ℂ X := (norm_withSeminorms ℂ X).toPolynormableSpace
  let : PolynormableSpace ℂ Y := (norm_withSeminorms ℂ Y).toPolynormableSpace
  obtain ⟨A, B, C, _, hC⟩ := exists_injectiveSeminorm_bound (Y := Y) univ (by simp)
    ((normSeminorm ℂ ℂ).comp l.toLinearMap) l.continuous.norm
  obtain ⟨a, ha, haA⟩ := Metric.mem_nhds_iff.mp A.property
  obtain ⟨b, hb, hbB⟩ := Metric.mem_nhds_iff.mp B.property
  let κ : E ⊗[ℂ] F →ₗ[ℂ] LocalBanach r := Completion.toComplL.toLinearMap.comp LinearMap.id
  have hκ (z : E ⊗[ℂ] F) : ‖κ z‖ = r z := localBanach_norm_coe r z
  -- Extend the bilinear map for r in both variables to the local Banach spaces.
  let D₀ : WithLocalSeminorm q →L[ℂ] WithLocalSeminorm s →L[ℂ] LocalBanach r :=
    ((TensorProduct.mk ℂ E F).compr₂ κ :
      WithLocalSeminorm q →ₗ[ℂ] WithLocalSeminorm s →ₗ[ℂ] LocalBanach r).mkContinuous₂ 1
      (fun x y ↦ by
        change ‖κ (x ⊗ₜ[ℂ] y)‖ ≤ 1 * q x * s y
        rw [hκ, one_mul]
        exact hr x y)
  let D₁ := D₀.fromCompletion
  let D := D₁.flip.fromCompletion
  have hD₀ : ‖D₀‖ ≤ 1 := LinearMap.mkContinuous₂_norm_le _ zero_le_one _
  have hD (x : LocalBanach q) (y : LocalBanach s) : ‖D y x‖ ≤ ‖x‖ * ‖y‖ := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      induction y using Completion.induction_on with
      | hp => exact isClosed_le (by fun_prop) (by fun_prop)
      | ih y =>
        change ‖D₁.flip.fromCompletion (y : LocalBanach s) (x : LocalBanach q)‖ ≤ _
        rw [ContinuousLinearMap.fromCompletion_apply_coe, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.fromCompletion_apply_coe, Completion.norm_coe, Completion.norm_coe]
        exact (D₀.le_opNorm₂ x y).trans
          (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hD₀ (norm_nonneg x)) (norm_nonneg y)))
  let c : ℝ≥0 := ⟨(C : ℝ) * (a⁻¹ * b⁻¹), by positivity⟩
  refine ⟨c, fun z ↦ ?_⟩
  obtain ⟨g, hg, hgz⟩ := exists_dual_vector'' ℂ (κ z)
  let k : F →L[ℂ] Y :=
    ((ContinuousLinearMap.compL ℂ (LocalBanach q) (LocalBanach r) ℂ g).comp D).comp j
  let S := TensorProduct.map i.toLinearMap k.toLinearMap
  have heq : l.toLinearMap.comp S = g.toLinearMap.comp κ := by
    apply TensorProduct.ext'
    intro x y
    change l (S (x ⊗ₜ[ℂ] y)) = g (κ (x ⊗ₜ[ℂ] y))
    rw [TensorProduct.map_tmul, hl]
    change k y (localBanachMap p q hq (i x)) = _
    rw [hi, localBanachMap_coe]
    change g (D (j y) ((show WithLocalSeminorm q from x) : LocalBanach q)) = _
    rw [hj]
    let x' : WithLocalSeminorm q := x
    let y' : WithLocalSeminorm s := y
    change g (D₁.flip.fromCompletion (y' : LocalBanach s) (x' : LocalBanach q)) = _
    rw [ContinuousLinearMap.fromCompletion_apply_coe, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.fromCompletion_apply_coe]
    rfl
  have hS : injectiveTensorSeminorm A B (S z) ≤ (a⁻¹ * b⁻¹) * injectiveTensorSeminorm V W z := by
    have : Nonempty (StrongDual.polar ℂ A.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    have : Nonempty (StrongDual.polar ℂ B.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    rw [(injectiveSeminorm_eq_ciSup A B (S z)).2]
    apply ciSup_le
    rintro ⟨φ, ψ⟩
    have hφ : ‖φ.val‖ ≤ a⁻¹ := by
      have hp : φ.val ∈ StrongDual.polar ℂ (Metric.ball 0 a) :=
        (topDualPairing ℂ X).flip.polar_antitone haA φ.property
      simpa only [NormedSpace.polar_ball ha, mem_closedBall_zero_iff] using hp
    have hψ : ‖ψ.val‖ ≤ b⁻¹ := by
      have hp : ψ.val ∈ StrongDual.polar ℂ (Metric.ball 0 b) :=
        (topDualPairing ℂ Y).flip.polar_antitone hbB ψ.property
      simpa only [NormedSpace.polar_ball hb, mem_closedBall_zero_iff] using hp
    have hcom : (tensorDualForm φ.val ψ.val).comp S =
        tensorDualForm (φ.val.comp i) (ψ.val.comp k) := by
      apply TensorProduct.ext'
      intro x y
      simp [S, tensorDualForm_tmul]
    change ‖((tensorDualForm φ.val ψ.val).comp S) z‖ ≤ _
    rw [hcom]
    refine norm_tensorDualForm_le_mul_injectiveSeminorm V W _ _ z (by positivity)
      (by positivity) (fun x hx ↦ ?_) (fun y hy ↦ ?_)
    · change ‖φ.val (i x)‖ ≤ a⁻¹
      exact (φ.val.le_opNorm (i x)).trans (mul_le_of_le_one_right (norm_nonneg _)
        (by rw [hi, localBanach_norm_coe]; exact hiV x hx)) |>.trans hφ
    · have hk : ‖k y‖ ≤ 1 := by
        refine (k y).opNorm_le_bound zero_le_one fun x ↦ ?_
        change ‖g (D (j y) x)‖ ≤ 1 * ‖x‖
        rw [one_mul]
        calc
          _ ≤ ‖D (j y) x‖ := (g.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hg)
          _ ≤ ‖x‖ * ‖j y‖ := hD _ _
          _ ≤ ‖x‖ := mul_le_of_le_one_right (norm_nonneg _) (by
            rw [hj, localBanach_norm_coe]
            exact hjW y hy)
      change ‖ψ.val (k y)‖ ≤ b⁻¹
      exact ((ψ.val.le_opNorm (k y)).trans (mul_le_of_le_one_right (norm_nonneg _) hk)).trans hψ
  have hz : l (S z) = (‖κ z‖ : ℂ) := (DFunLike.congr_fun heq z).trans hgz
  calc
    r z = ‖l (S z)‖ := by rw [hz, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), hκ]
    _ ≤ C * injectiveTensorSeminorm A B (S z) := hC _
    _ ≤ (c : ℝ) * _ := by
      change _ ≤ (C : ℝ) * (a⁻¹ * b⁻¹) * _
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hS C.coe_nonneg


/-- The injective unit-ball seminorm of a pure tensor is bounded by the product
of the norms of its factors. -/
private theorem injectiveTensorNorm_tmul_le {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (x : G) (y : H) :
    injectiveTensorNorm G H (x ⊗ₜ[ℂ] y) ≤ ‖x‖ * ‖y‖ := by
  let : PolynormableSpace ℂ G := (norm_withSeminorms ℂ G).toPolynormableSpace
  let : PolynormableSpace ℂ H := (norm_withSeminorms ℂ H).toPolynormableSpace
  let U : {U : Set G // U ∈ 𝓝 0} := ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩
  let V : {V : Set H // V ∈ 𝓝 0} := ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩
  have : Nonempty (StrongDual.polar ℂ U.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  have : Nonempty (StrongDual.polar ℂ V.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  change injectiveTensorSeminorm U V _ ≤ _
  rw [(injectiveSeminorm_eq_ciSup U V _).2]
  apply ciSup_le
  rintro ⟨φ, ψ⟩
  have hφ : ‖φ.val‖ ≤ 1 := by
    simpa [U, NormedSpace.polar_closedBall (𝕜 := ℂ) one_pos, mem_closedBall_zero_iff] using φ.property
  have hψ : ‖ψ.val‖ ≤ 1 := by
    simpa [V, NormedSpace.polar_closedBall (𝕜 := ℂ) one_pos, mem_closedBall_zero_iff] using ψ.property
  rw [tensorDualForm_tmul, norm_mul]
  exact mul_le_mul ((φ.val.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) hφ))
    ((ψ.val.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _) hψ))
    (norm_nonneg _) (norm_nonneg _)

/-- Paper: Theorem C.2.4.9, p. 688. Nuclearity gives an injective bound on the
evaluation pairing. The bound passes to the local Banach space by density. -/
private theorem exists_integral_localBanachMap
    {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    (h : IsNuclearTVS.{v, u} E)
    (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U) :
    ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
      let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
      let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
      IsIntegralBilinearForm (fun (x : LocalBanach p) (φ : StrongDual ℂ (LocalBanach q)) ↦
        φ (localBanachMap p q (gauge_mono (absorbent_nhds_zero hV) hVU) x)) := by
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
  let Y := StrongDual ℂ (LocalBanach q)
  let F := ULift.{v} Y
  let : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  obtain ⟨j, hj⟩ := exists_localBanach_inclusion q (continuous_gauge cU hU)
  let B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun x f ↦ f.down (j x))
    (by intros; simp) (by intros; simp) (by intros; rfl) (by intros; rfl)
  let L := TensorProduct.lift B
  let r := (normSeminorm ℂ ℂ).comp L
  have hr : ContinuousAt (fun z : E × F ↦ r (z.1 ⊗ₜ[ℂ] z.2)) 0 :=
    ((ContinuousLinearMap.apply ℂ (E' := LocalBanach q) ℂ).continuous₂.comp
      ((j.continuous.comp continuous_fst).prodMk
        (continuous_uliftDown.comp continuous_snd))).norm.continuousAt
  have he := h.2.2 F inferInstance inferInstance inferInstance inferInstance inferInstance
  let e := he.homeomorph
  have hback : Continuous (show InjectiveTensor E F → ProjectiveTensor E F from id) :=
    e.continuous_symm.congr fun z ↦ e.apply_symm_apply z
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
      ContinuousAt (fun z : E × F ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
  have hr' : @Continuous (InjectiveTensor E F) ℝ _ _ r :=
    (hP.continuous_seminorm ⟨r, hr⟩).comp hback
  obtain ⟨A, W, C, hAU, hC⟩ := exists_injectiveSeminorm_bound U hU r hr'
  obtain ⟨p₀, hp₀, hVA⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp A.property
  let V := p₀.ball 0 1
  have hV : V ∈ 𝓝 0 := p₀.ball_mem_nhds hp₀ one_pos
  have bV : Balanced ℂ V := p₀.balanced_ball_zero 1
  have cV : Convex ℝ V := p₀.convex_ball 0 1
  have hVU : V ⊆ U := hVA.trans hAU
  let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
  let X := LocalBanach p
  let T := localBanachMap p q (gauge_mono (absorbent_nhds_zero hV) hVU)
  let : PolynormableSpace ℂ X := (norm_withSeminorms ℂ X).toPolynormableSpace
  let : PolynormableSpace ℂ Y := (norm_withSeminorms ℂ Y).toPolynormableSpace
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.mp W.property
  have extend (φ : StrongDual.polar ℂ A.val) :
      ∃ g : StrongDual ℂ X, ‖g‖ ≤ 1 ∧
        ∀ x : WithLocalSeminorm p, g (x : X) = φ.val x := by
    have bound (x : WithLocalSeminorm p) : ‖φ.val x‖ ≤ ‖x‖ := by
      change ‖φ.val x‖ ≤ gauge V x
      apply le_csInf (absorbent_nhds_zero hV).gauge_set_nonempty
      rintro a ⟨ha, y, hy, hxy⟩
      change (a • y : E) = (show E from x) at hxy
      change ‖φ.val (show E from x)‖ ≤ a
      have hmap : φ.val (a • y) = a • φ.val y := φ.val.toLinearMap.map_smul_of_tower a y
      rw [← hxy, hmap, norm_smul, Real.norm_of_nonneg ha.le]
      exact mul_le_of_le_one_right ha.le ((StrongDual.mem_polar_iff ℂ _).mp φ.property _ (hVA hy))
    let f := (show WithLocalSeminorm p →ₗ[ℂ] ℂ from φ.val.toLinearMap).mkContinuous 1
      (fun x ↦ (bound x).trans_eq (one_mul _).symm)
    refine ⟨f.fromCompletion, f.fromCompletion.opNorm_le_bound zero_le_one fun x ↦ ?_,
      fun x ↦ f.fromCompletion_apply_coe x⟩
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      rw [ContinuousLinearMap.fromCompletion_apply_coe, Completion.norm_coe, one_mul]
      exact bound x
  let L' : X ⊗[ℂ] Y →ₗ[ℂ] ℂ :=
    TensorProduct.lift (LinearMap.mk₂ ℂ (fun x f ↦ f (T x))
      (by intros; simp) (by intros; simp) (by intros; rfl) (by intros; rfl))
  let ε := injectiveTensorNorm X Y
  -- Establish the bound first when the first coordinates come from E.
  have bound (n : ℕ) (x : Fin n → WithLocalSeminorm p) (f : Fin n → Y) :
      ‖L' (∑ i, (x i : X) ⊗ₜ[ℂ] f i)‖ ≤ (C * δ⁻¹) * ε (∑ i, (x i : X) ⊗ₜ[ℂ] f i) := by
    let z : E ⊗[ℂ] F := ∑ i, (show E from x i) ⊗ₜ[ℂ] (ULift.up (f i) : F)
    have hz : L' (∑ i, (x i : X) ⊗ₜ[ℂ] f i) = L z := by
      simp only [z, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      let x' : E := x i
      exact congrArg (f i) ((localBanachMap_coe p q _ (x i)).trans (hj x').symm)
    have hε : injectiveTensorSeminorm A W z ≤ δ⁻¹ * ε (∑ i, (x i : X) ⊗ₜ[ℂ] f i) := by
      have : Nonempty (StrongDual.polar ℂ A.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
      have : Nonempty (StrongDual.polar ℂ W.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
      rw [(injectiveSeminorm_eq_ciSup A W z).2]
      apply ciSup_le
      rintro ⟨φ, ψ⟩
      obtain ⟨g, hg, hgx⟩ := extend φ
      let up : Y →L[ℂ] F := (ContinuousLinearEquiv.ulift : F ≃L[ℂ] Y).symm.toContinuousLinearMap
      have hψ : ‖ψ.val‖ ≤ δ⁻¹ := by
        have hp : ψ.val ∈ StrongDual.polar ℂ (Metric.ball 0 δ) :=
          (topDualPairing ℂ F).flip.polar_antitone hδW ψ.property
        simpa only [NormedSpace.polar_ball hδ, mem_closedBall_zero_iff] using hp
      have heq : tensorDualForm φ.val ψ.val z =
          tensorDualForm g (ψ.val.comp up) (∑ i, (x i : X) ⊗ₜ[ℂ] f i) := by
        simp only [z, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        let x' : E := x i
        change tensorDualForm φ.val ψ.val (x' ⊗ₜ[ℂ] (ULift.up (f i) : F)) =
          tensorDualForm g (ψ.val.comp up) ((x i : X) ⊗ₜ[ℂ] f i)
        rw [tensorDualForm_tmul, tensorDualForm_tmul]
        exact congrArg (fun c ↦ c * ψ.val (ULift.up (f i))) (hgx (x i)).symm
      rw [heq, ← one_mul δ⁻¹]
      apply norm_tensorDualForm_le_mul_injectiveSeminorm _ _ _ _ _ one_pos (inv_pos.mpr hδ)
      · intro x hx
        exact (g.le_opNorm x).trans (by simpa only [one_mul] using
          (mul_le_mul hg (mem_closedBall_zero_iff.mp hx) (norm_nonneg _) zero_le_one))
      · intro y hy
        change ‖ψ.val (ULift.up y)‖ ≤ δ⁻¹
        exact (ψ.val.le_opNorm _).trans (by
          rw [ULift.norm_up]
          exact (mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.mp hy)).trans hψ)
    rw [hz]
    exact (hC z).trans (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hε C.coe_nonneg))
  have hbound (z : X ⊗[ℂ] Y) : ‖L' z‖ ≤ (C * δ⁻¹) * ε z := by
    obtain ⟨n, x, f, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
    have hd : DenseRange (fun ys : Fin n → WithLocalSeminorm p ↦ fun i ↦ (ys i : X)) :=
      DenseRange.piMap fun _ ↦ Completion.denseRange_coe
    refine hd.induction_on x (isClosed_le ?_ ?_) (fun ys ↦ bound n ys f)
    · simp only [map_sum]
      exact (continuous_finsetSum _ fun i _ ↦
        ((f i).continuous.comp T.continuous).comp (continuous_apply i)).norm
    · let S (y : Y) : X →L[ℂ] WithLocalSeminorm ε :=
        ((TensorProduct.mk ℂ X Y).flip y).mkContinuous ‖y‖ (fun x ↦ by
          change ε (x ⊗ₜ[ℂ] y) ≤ ‖y‖ * ‖x‖
          rw [mul_comm]
          exact injectiveTensorNorm_tmul_le x y)
      change Continuous (fun ys : Fin n → X ↦ (C * δ⁻¹) * ‖∑ i, S (f i) (ys i)‖)
      exact continuous_const.mul (continuous_finsetSum _ fun i _ ↦
        (S (f i)).continuous.comp (continuous_apply i)).norm
  let A' : {U : Set X // U ∈ 𝓝 0} := ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩
  let W' : {V : Set Y // V ∈ 𝓝 0} := ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩
  let c : ℝ≥0 := ⟨C * δ⁻¹, by positivity⟩
  let hI := withGeneratingSeminorms_spec (X ⊗[ℂ] Y)
    (fun UV : {U : Set X // U ∈ 𝓝 0} × {V : Set Y // V ∈ 𝓝 0} ↦
      injectiveTensorSeminorm UV.1 UV.2)
  let l : InjectiveTensor X Y →ₗ[ℂ] ℂ := L'
  let s : Seminorm ℂ (InjectiveTensor X Y) := ε
  have hs : Continuous (c • s : Seminorm ℂ (InjectiveTensor X Y)) :=
    (hI.continuous_seminorm (A', W')).const_smul c
  have hle : (normSeminorm ℂ ℂ).comp l ≤ c • s := fun z ↦ hbound z
  have hcont : Continuous l :=
    (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp l fun _ ↦
      Seminorm.continuous_of_le hs hle
  exact ⟨V, hV, bV, cV, hVU, ⟨l, hcont⟩, fun _ _ ↦ rfl⟩

/-- Paper: Theorem C.2.4.9, p. 688. Nuclearity is equivalent to the existence
of a smaller balanced convex zero-neighborhood for each such neighborhood
so that the comparison map between local Banach spaces induces an integral form. -/
theorem isNuclearTVS_iff_localBanach_integral
    (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [T2Space E] :
    IsNuclearTVS.{v, u} E ↔
      ∀ (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U),
        ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
          let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
          let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
          let T := localBanachMap p q (gauge_mono (absorbent_nhds_zero hV) hVU)
          IsIntegralBilinearForm (fun (x : LocalBanach p) (φ : StrongDual ℂ (LocalBanach q)) ↦
            φ (T x)) := by
  constructor
  · intro h
    exact exists_integral_localBanachMap h
  · intro h
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro F _ _ _ _ _
    have := PolynormableSpace.isTopologicalAddGroup ℂ E
    let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun r : {r : Seminorm ℂ (E ⊗[ℂ] F) //
        ContinuousAt (fun z : E × F ↦ r (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ r.val)
    have hback : Continuous (show InjectiveTensor E F → ProjectiveTensor E F from id) := by
      refine hP.continuous_of_continuous_comp
        (LinearMap.id : InjectiveTensor E F →ₗ[ℂ] ProjectiveTensor E F) fun ⟨r, hr⟩ ↦ ?_
      obtain ⟨q, s, hq, hs, hrs⟩ := exists_projectiveSeminorm_pure_bound E r hr
      let U := q.ball 0 1
      have hU : U ∈ 𝓝 0 := q.ball_mem_nhds hq one_pos
      obtain ⟨V, hV, bV, cV, hVU, hT⟩ :=
        h U hU (q.balanced_ball_zero 1) (q.convex_ball 0 1)
      let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
      obtain ⟨i, hi⟩ := exists_localBanach_inclusion p (continuous_gauge cV hV)
      obtain ⟨j, hj⟩ := exists_localBanach_inclusion s hs
      have hqeq : gaugeSeminorm (q.balanced_ball_zero 1) (q.convex_ball 0 1)
          (absorbent_nhds_zero hU) = q :=
        DFunLike.coe_injective (q.restrictScalars ℝ).gauge_ball
      let V' : {V : Set E // V ∈ 𝓝 0} := ⟨V, hV⟩
      let W : {W : Set F // W ∈ 𝓝 0} := ⟨s.ball 0 1, s.ball_mem_nhds hs one_pos⟩
      have hrs' : ∀ x y, r (x ⊗ₜ[ℂ] y) ≤
          gaugeSeminorm (q.balanced_ball_zero 1) (q.convex_ball 0 1) (absorbent_nhds_zero hU) x * s y := by
        rw [hqeq]
        exact hrs
      obtain ⟨C, hC⟩ := projectiveSeminorm_le_of_localBanach_integral
        (gauge_mono (absorbent_nhds_zero hV) hVU) V' W i j hi hj
        (fun _ hx ↦ gauge_le_one_of_mem hx) (fun _ hy ↦ (s.mem_ball_zero.mp hy).le)
        r hrs' hT
      let hI := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
        (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
          injectiveTensorSeminorm UV.1 UV.2)
      exact Seminorm.continuous_of_le (q := C • injectiveTensorSeminorm V' W)
        ((hI.continuous_seminorm (V', W)).const_smul C) hC
    exact (⟨Equiv.refl (E ⊗[ℂ] F), (uniformContinuous_tensorComparison E F).continuous, hback⟩ :
      ProjectiveTensor E F ≃ₜ InjectiveTensor E F).isHomeomorph


end IntegralComparisons

section Permanence

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Evaluating an equicontinuous family of weak dual functionals is continuous into
the uniform norm on continuous functions on a compact parameter space. -/
private def weakDualEvaluationCLM {X K : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [TopologicalSpace K] [CompactSpace K]
    (a : K → WeakDual ℂ X) (ha : Continuous a)
    (he : EquicontinuousAt (fun k x ↦ a k x) 0) : X →L[ℂ] C(K, ℂ) := by
  let f : X →ₗ[ℂ] C(K, ℂ) :=
    { toFun x := ⟨fun k ↦ a k x, (WeakDual.eval_continuous x).comp ha⟩
      map_add' x y := ContinuousMap.ext fun k ↦ map_add (a k) x y
      map_smul' c x := ContinuousMap.ext fun k ↦ map_smul (a k) c x }
  refine ⟨f, continuous_of_continuousAt_zero f ?_⟩
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.equicontinuousAt_iff_right.mp he ε hε] with x hx
  rw [dist_zero_right, ContinuousMap.norm_lt_iff _ hε]
  intro k
  simpa only [f, LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk,
    map_zero, dist_zero_left] using hx k

set_option maxHeartbeats 500000 in
/-- Every continuous seminorm on a nuclear space is bounded by the norm of a
continuous linear map into a Hilbert space, up to a constant. -/
theorem exists_hilbert_domination (hE : IsNuclearTVS.{v, u} E)
    (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (H : Type (max v u)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (a : E →L[ℂ] H) (C : ℝ), 0 ≤ C ∧ ∀ x, q x ≤ C * ‖a x‖ := by
  let := hE.1
  let := hE.2.1
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  let Y := ULift.{v} (StrongDual ℂ (LocalBanach q))
  let : PolynormableSpace ℂ Y := (norm_withSeminorms ℂ Y).toPolynormableSpace
  obtain ⟨j, hj⟩ := exists_localBanach_inclusion q hq
  let b : E →ₗ[ℂ] Y →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun x y ↦ y.down (j x))
    (by intros; simp) (by intros; simp) (by intros; rfl) (by intros; rfl)
  have hb : Continuous (fun z : E × Y ↦ b z.1 z.2) :=
    (ContinuousLinearMap.apply ℂ (E' := LocalBanach q) ℂ).continuous₂.comp
      ((j.continuous.comp continuous_fst).prodMk (continuous_uliftDown.comp continuous_snd))
  let l : InjectiveTensor E Y →ₗ[ℂ] ℂ := TensorProduct.lift b
  let r := (normSeminorm ℂ ℂ).comp l
  let e := (hE.2.2 Y inferInstance inferInstance inferInstance inferInstance inferInstance).homeomorph
  have hback : Continuous (show InjectiveTensor E Y → ProjectiveTensor E Y from id) :=
    e.continuous_symm.congr fun z ↦ e.apply_symm_apply z
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] Y)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] Y) //
      ContinuousAt (fun z : E × Y ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
  have hr : Continuous r := (hP.continuous_seminorm ⟨r, hb.norm.continuousAt⟩).comp hback
  have hl : Continuous l :=
    (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp l fun _ ↦ hr
  obtain ⟨A, B, _, _, hA, hB, heA, heB, μ, _, _, hμ, hrep⟩ :=
    (isIntegralBilinearForm_iff_radon b hb).mp ⟨⟨l, hl⟩, fun _ _ ↦ rfl⟩
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let : MeasurableSpace (A × B) := borel (A × B)
  let : BorelSpace (A × B) := ⟨rfl⟩
  let : IsFiniteMeasure μ := ⟨hμ.trans_lt ENNReal.one_lt_top⟩
  let J := ContinuousMap.toLp 2 μ ℂ (E := ℂ)
  let f : E →L[ℂ] C(A × B, ℂ) :=
    weakDualEvaluationCLM (fun k ↦ k.1.val) (continuous_subtype_val.comp continuous_fst)
      (heA.comp Prod.fst)
  let g : Y →L[ℂ] C(A × B, ℂ) :=
    weakDualEvaluationCLM (fun k ↦ k.2.val) (continuous_subtype_val.comp continuous_snd)
      (heB.comp Prod.snd)
  refine ⟨Lp ℂ 2 μ, inferInstance, inferInstance, inferInstance, J.comp f, ‖J‖ * ‖g‖,
    by positivity, fun x ↦ ?_⟩
  obtain ⟨y, hy, hyx⟩ := exists_dual_vector'' ℂ (j x)
  let y' : Y := ULift.up y
  have hinner : inner ℂ (J (star (g y'))) (J (f x)) = b x y' := by
    rw [L2.inner_def]
    refine (integral_congr_ae ?_).trans (hrep x y').2.symm
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (star (g y')),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (f x)] with k hk₁ hk₂
    rw [hk₁, hk₂, RCLike.inner_apply, ContinuousMap.star_apply]
    change k.1.val x * star (star (k.2.val y')) = _
    rw [star_star]
  have hnorm : ‖J (star (g y'))‖ ≤ ‖J‖ * ‖g‖ := by
    have hy' : ‖y'‖ ≤ 1 := hy
    have hg : ‖g y'‖ ≤ ‖g‖ :=
      (g.le_opNorm y').trans (mul_le_of_le_one_right (norm_nonneg g) hy')
    calc
      _ ≤ ‖J‖ * ‖star (g y')‖ := J.le_opNorm _
      _ = ‖J‖ * ‖g y'‖ := by rw [norm_star]
      _ ≤ ‖J‖ * ‖g‖ := mul_le_mul_of_nonneg_left hg (norm_nonneg J)
  have heq : b x y' = (‖j x‖ : ℂ) := hyx
  calc
    q x = ‖b x y'‖ := by rw [heq, Complex.norm_of_nonneg (norm_nonneg _), hj, localBanach_norm_coe]
    _ ≤ _ := hinner ▸ (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

/-- Paper: Lemma C.2.4.10(1), p. 689. A linear subspace of a nuclear space is
nuclear for its subspace topology. -/
theorem isNuclearTVS_submodule (hE : IsNuclearTVS.{v, u} E) (S : Submodule ℂ E) :
    IsNuclearTVS.{v, u} S := by
  let := hE.1
  let := hE.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro F _ _ _ _ _
  let i : S →L[ℂ] E := ⟨S.subtype, continuous_subtype_val⟩
  let M := injectiveTensorMap i.toLinearMap (ContinuousLinearMap.id ℂ F).toLinearMap
  have hM : Continuous M := injectiveTensorMap_continuous i (ContinuousLinearMap.id ℂ F)
  let e := (hE.2.2 F inferInstance inferInstance inferInstance inferInstance inferInstance).homeomorph
  have hEback : Continuous (show InjectiveTensor E F → ProjectiveTensor E F from id) :=
    e.continuous_symm.congr fun z ↦ e.apply_symm_apply z
  have hback : Continuous (show InjectiveTensor S F → ProjectiveTensor S F from id) := by
    let hP := withGeneratingSeminorms_spec (S ⊗[ℂ] F)
      (fun p : {p : Seminorm ℂ (S ⊗[ℂ] F) //
        ContinuousAt (fun z : S × F ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
    refine hP.continuous_of_continuous_comp
      (LinearMap.id : InjectiveTensor S F →ₗ[ℂ] ProjectiveTensor S F) fun ⟨r, hr⟩ ↦ ?_
    obtain ⟨q, s, hq, hs, hbound⟩ := exists_projectiveSeminorm_pure_bound S r hr
    obtain ⟨p, hp, hqp⟩ := Seminorm.exists_le_comp_of_isInducing hq (f := S.subtype) .subtypeVal
    obtain ⟨H, _, _, _, a, C, _, ha⟩ := exists_hilbert_domination hE p hp
    let aS := a.toLinearMap.comp S.subtype
    let K := aS.range.topologicalClosure
    let aK := (Submodule.inclusion aS.range.le_topologicalClosure).comp aS.rangeRestrict
    have hd : DenseRange aK :=
      ((denseRange_inclusion_iff aS.range.le_topologicalClosure).mpr subset_rfl).comp
        aS.surjective_rangeRestrict.denseRange (continuous_inclusion _)
    let : CompleteSpace K := aS.range.isClosed_topologicalClosure.completeSpace_coe
    -- Extend the bilinear map for r through the closure of the image of S in H.
    let κ : S ⊗[ℂ] F →ₗ[ℂ] LocalBanach r := Completion.toComplL.toLinearMap.comp LinearMap.id
    let B : WithLocalSeminorm q →ₗ[ℂ] WithLocalSeminorm s →ₗ[ℂ] LocalBanach r :=
      (TensorProduct.mk ℂ S F).compr₂ κ
    have hB (x : WithLocalSeminorm q) (y : WithLocalSeminorm s) :
        ‖B x y‖ ≤ 1 * ‖x‖ * ‖y‖ := by
      change ‖κ (x ⊗ₜ[ℂ] y)‖ ≤ 1 * q x * s y
      rw [show ‖κ (x ⊗ₜ[ℂ] y)‖ = r (x ⊗ₜ[ℂ] y) from localBanach_norm_coe r _, one_mul]
      exact hbound x y
    let D := B.mkContinuous₂ 1 hB
    let Dc := D.flip.fromCompletion
    let d : S →ₗ[ℂ] LocalBanach s →L[ℂ] LocalBanach r := Dc.flip.toLinearMap
    have hd_coe (x : S) (y : WithLocalSeminorm s) : d x y = D x y := by
      change Dc y x = D x y
      rw [show Dc y = D.flip y from D.flip.fromCompletion_apply_coe y]
      rfl
    have hD : ‖D‖ ≤ 1 := LinearMap.mkContinuous₂_norm_le _ zero_le_one _
    have hd_norm (x : S) : ‖d x‖ ≤ q x := by
      refine (d x).opNorm_le_bound (apply_nonneg q x) fun y ↦ ?_
      induction y using Completion.induction_on with
      | hp => exact isClosed_le (by fun_prop) (by fun_prop)
      | ih y =>
        rw [hd_coe, Completion.norm_coe]
        exact (D.le_opNorm₂ x y).trans
          (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (apply_nonneg q x) hD) (norm_nonneg y))
    have hda (x : S) : ‖d x‖ ≤ C * ‖aK x‖ :=
      (hd_norm x).trans ((hqp x).trans (ha x))
    let dK := LinearMap.extendOfNorm (σ₁₂ := RingHom.id ℂ)
      (F := LocalBanach s →L[ℂ] LocalBanach r) d aK
    let D' := (dK.comp K.orthogonalProjectionOnto).comp a
    have hD' (x : S) : D' x = d x := by
      change dK (K.orthogonalProjectionOnto (a x)) = d x
      rw [show K.orthogonalProjectionOnto (a x) = aK x from
        K.orthogonalProjectionOnto_mem_subspace_eq_self (aK x)]
      exact LinearMap.extendOfNorm_eq (σ₁₂ := RingHom.id ℂ) (f := d) hd ⟨C, hda⟩ x
    obtain ⟨j, hj⟩ := exists_localBanach_inclusion s hs
    let b : E →ₗ[ℂ] F →ₗ[ℂ] LocalBanach r :=
      LinearMap.mk₂ ℂ (fun x y ↦ D' x (j y))
        (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
    let R := (normSeminorm ℂ (LocalBanach r)).comp (TensorProduct.lift b)
    have hR : ContinuousAt (fun z : E × F ↦ R (z.1 ⊗ₜ[ℂ] z.2)) 0 := by
      change ContinuousAt (fun z : E × F ↦ ‖D' z.1 (j z.2)‖) 0
      exact ((D'.continuous.comp continuous_fst).clm_apply
        (j.continuous.comp continuous_snd)).norm.continuousAt
    have hκ : (TensorProduct.lift b).comp M = κ := by
      apply TensorProduct.ext'
      intro x y
      change (TensorProduct.lift b) (TensorProduct.map S.subtype LinearMap.id (x ⊗ₜ[ℂ] y)) = _
      rw [TensorProduct.map_tmul, TensorProduct.lift.tmul, LinearMap.id_apply]
      change D' x (j y) = κ (x ⊗ₜ[ℂ] y)
      rw [hD', hj, hd_coe]
      rfl
    let hP' := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
        ContinuousAt (fun z : E × F ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
    have hcont := ((hP'.continuous_seminorm ⟨R, hR⟩).comp hEback).comp hM
    exact hcont.congr fun z ↦ by
      change ‖((TensorProduct.lift b).comp M) z‖ = r z
      rw [hκ]
      exact localBanach_norm_coe r z
  exact (⟨Equiv.refl (S ⊗[ℂ] F), (uniformContinuous_tensorComparison S F).continuous, hback⟩ :
    ProjectiveTensor S F ≃ₜ InjectiveTensor S F).isHomeomorph

open scoped NNReal in
/-- Tensoring with a fixed vector in the second factor is continuous for the
projective topology. -/
private theorem continuous_projectiveTensor_tmul_right {H F : Type*}
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] [PolynormableSpace ℂ H]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]
    (y : F) : Continuous (fun x : H ↦ (show ProjectiveTensor H F from x ⊗ₜ[ℂ] y)) := by
  have := PolynormableSpace.isTopologicalAddGroup ℂ H
  let f : H →ₗ[ℂ] ProjectiveTensor H F := (TensorProduct.mk ℂ H F).flip y
  change Continuous f
  let hP := withGeneratingSeminorms_spec (H ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (H ⊗[ℂ] F) //
      ContinuousAt (fun v : H × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
  refine hP.continuous_of_continuous_comp f fun ⟨r, hr⟩ ↦ ?_
  obtain ⟨p, q, hp, _, hpq⟩ := exists_projectiveSeminorm_pure_bound H r hr
  let c : ℝ≥0 := ⟨q y, apply_nonneg q y⟩
  refine Seminorm.continuous_of_le (q := c • p)
    (hp.const_smul _) fun x ↦ ?_
  change r (x ⊗ₜ[ℂ] y) ≤ q y * p x
  rw [mul_comm]
  exact hpq x y

omit [TopologicalSpace E] in
/-- If a seminorm on a quotient tensor product pulls back to a
seminorm bounded by an injective seminorm through a Hilbert space, it still obeys
that bound after projecting away the closure of the image of the submodule. -/
private theorem quotientTensorSeminorm_le_projection {H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]
    (S : Submodule ℂ E) (a : E →ₗ[ℂ] H) (r : Seminorm ℂ ((E ⧸ S) ⊗[ℂ] F))
    (W : {W : Set H // W ∈ 𝓝 0}) (V : {V : Set F // V ∈ 𝓝 0}) (C : ℝ)
    (h : ∀ z, r (TensorProduct.map S.mkQ LinearMap.id z) ≤
      C * injectiveTensorSeminorm W V (TensorProduct.map a LinearMap.id z))
    (z : E ⊗[ℂ] F) :
    r (TensorProduct.map S.mkQ LinearMap.id z) ≤
      C * injectiveTensorSeminorm W V
        (TensorProduct.map (((S.map a).topologicalClosure)ᗮ.starProjection.toLinearMap.comp a)
          LinearMap.id z) := by
  let : PolynormableSpace ℂ H := (norm_withSeminorms ℂ H).toPolynormableSpace
  let K := (S.map a).topologicalClosure
  let : CompleteSpace K := (S.map a).isClosed_topologicalClosure.completeSpace_coe
  let T : E ⊗[ℂ] F →ₗ[ℂ] (E ⧸ S) ⊗[ℂ] F := TensorProduct.map S.mkQ LinearMap.id
  let A : E ⊗[ℂ] F →ₗ[ℂ] ProjectiveTensor H F := TensorProduct.map a LinearMap.id
  let P : E ⊗[ℂ] F →ₗ[ℂ] ProjectiveTensor H F :=
    TensorProduct.map (Kᗮ.starProjection.toLinearMap.comp a) LinearMap.id
  have hlift (z : E ⊗[ℂ] F) : ∃ z' : ℕ → E ⊗[ℂ] F,
      (∀ n, T (z' n) = T z) ∧ Tendsto (fun n ↦ A (z' n)) atTop (𝓝 (P z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      have hx : K.starProjection (a x) ∈ closure (S.map a : Set H) :=
        K.starProjection_apply_mem _
      obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp hx
      choose t ht ht' using hs
      refine ⟨fun n ↦ (x - t n) ⊗ₜ[ℂ] y, fun n ↦ ?_, ?_⟩
      · have hn : S.mkQ (t n) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr (ht n)
        simp only [T, TensorProduct.map_tmul, LinearMap.id_apply, map_sub, hn, sub_zero]
      · have hsub : Tendsto (fun n ↦ a x - s n) atTop (𝓝 (Kᗮ.starProjection (a x))) := by
          rw [Submodule.starProjection_orthogonal_val]
          exact tendsto_const_nhds.sub hlim
        have hA (n : ℕ) : A ((x - t n) ⊗ₜ[ℂ] y) = (a x - s n) ⊗ₜ[ℂ] y := by
          change TensorProduct.map a LinearMap.id ((x - t n) ⊗ₜ[ℂ] y) = _
          rw [TensorProduct.map_tmul, LinearMap.id_apply, map_sub, ht']
        have hP : P (x ⊗ₜ[ℂ] y) = Kᗮ.starProjection (a x) ⊗ₜ[ℂ] y := by
          change TensorProduct.map (Kᗮ.starProjection.toLinearMap.comp a) LinearMap.id
            (x ⊗ₜ[ℂ] y) = _
          rw [TensorProduct.map_tmul, LinearMap.id_apply]
          rfl
        simp_rw [hA, hP]
        exact (continuous_projectiveTensor_tmul_right y).continuousAt.tendsto.comp hsub
    | add x y hx hy =>
      obtain ⟨x', hx', hxlim⟩ := hx
      obtain ⟨y', hy', hylim⟩ := hy
      exact ⟨fun n ↦ x' n + y' n, fun n ↦ by simp [hx', hy'], by
        simpa only [map_add] using hxlim.add hylim⟩
  obtain ⟨z', hz', hzlim⟩ := hlift z
  let hP := withGeneratingSeminorms_spec (H ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (H ⊗[ℂ] F) //
      ContinuousAt (fun v : H × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
  have hcont : Continuous (show ProjectiveTensor H F → ℝ from injectiveTensorSeminorm W V) :=
    hP.continuous_seminorm ⟨_, injectiveSeminorm_continuousAt_tmul W V⟩
  change r (T z) ≤ C * injectiveTensorSeminorm W V (P z)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds
    ((hcont.continuousAt.tendsto.comp hzlim).const_mul C) fun n ↦ by
      rw [← hz' n]
      exact h (z' n)

/-- Paper: Lemma C.2.4.10(1), p. 689. A Hausdorff quotient of a nuclear space is nuclear. -/
theorem isNuclearTVS_quotient (hE : IsNuclearTVS.{v, u} E) (S : Submodule ℂ E)
    [T2Space (E ⧸ S)] : IsNuclearTVS.{v, u} (E ⧸ S) := by
  classical
  let := hE.1
  let := hE.2.1
  let Q := E ⧸ S
  let : PolynormableSpace ℂ Q := polynormableSpace_quotient S
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro F _ _ _ _ _
  let e := (hE.2.2 F inferInstance inferInstance inferInstance inferInstance inferInstance).homeomorph
  have hbackE : Continuous (show InjectiveTensor E F → ProjectiveTensor E F from id) :=
    e.continuous_symm.congr fun z ↦ e.apply_symm_apply z
  have hback : Continuous (show InjectiveTensor Q F → ProjectiveTensor Q F from id) := by
    let hP := withGeneratingSeminorms_spec (Q ⊗[ℂ] F)
      (fun p : {p : Seminorm ℂ (Q ⊗[ℂ] F) //
        ContinuousAt (fun v : Q × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
    refine hP.continuous_of_continuous_comp
      (LinearMap.id : InjectiveTensor Q F →ₗ[ℂ] ProjectiveTensor Q F) fun ⟨r, hr⟩ ↦ ?_
    let T : E ⊗[ℂ] F →ₗ[ℂ] Q ⊗[ℂ] F := TensorProduct.map S.mkQ LinearMap.id
    let R : Seminorm ℂ (InjectiveTensor E F) := r.comp T
    have hR : ContinuousAt (fun v : E × F ↦ R (v.1 ⊗ₜ[ℂ] v.2)) 0 := by
      have hq : Continuous (fun v : E × F ↦ (S.mkQ v.1, v.2)) :=
        (S.mkQL.continuous.comp continuous_fst).prodMk continuous_snd
      refine (hr.comp_of_eq hq.continuousAt (by simp)).congr (Eventually.of_forall fun v ↦ ?_)
      change r (S.mkQ v.1 ⊗ₜ[ℂ] v.2) =
        r (TensorProduct.map S.mkQ LinearMap.id (v.1 ⊗ₜ[ℂ] v.2))
      rw [TensorProduct.map_tmul, LinearMap.id_apply]
    let hPE := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
        ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
    have hRc : Continuous R :=
      (hPE.continuous_seminorm ⟨R, hR⟩).comp hbackE
    obtain ⟨U, V, C, _, hC⟩ := exists_injectiveSeminorm_bound univ univ_mem R hRc
    obtain ⟨p, hp, hpU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp U.property
    obtain ⟨H, _, _, _, a, D, hD, ha⟩ := exists_hilbert_domination hE p hp
    let : PolynormableSpace ℂ H := (norm_withSeminorms ℂ H).toPolynormableSpace
    let W : {W : Set H // W ∈ 𝓝 0} := ⟨Metric.ball 0 (D + 1)⁻¹,
      Metric.ball_mem_nhds 0 (by positivity)⟩
    let L := a.toLinearMap.range.topologicalClosure
    let aL := (Submodule.inclusion a.toLinearMap.range.le_topologicalClosure).comp
      a.toLinearMap.rangeRestrict
    have hd : DenseRange aL :=
      ((denseRange_inclusion_iff a.toLinearMap.range.le_topologicalClosure).mpr subset_rfl).comp
        a.toLinearMap.surjective_rangeRestrict.denseRange (continuous_inclusion _)
    let : CompleteSpace L := a.toLinearMap.range.isClosed_topologicalClosure.completeSpace_coe
    -- Each functional in the original polar extends along a to a functional on H.
    have hfactor (φ : StrongDual.polar ℂ U.val) :
        ∃ ψ : StrongDual.polar ℂ W.val, ψ.val.comp a = φ.val := by
      have hpφ (x : E) : ‖φ.val x‖ ≤ p x := by
        let B := p.ball 0 1
        have hB := (p.restrictScalars ℝ).absorbent_ball_zero one_pos
        rw [← show gauge B x = p x from congrFun (p.restrictScalars ℝ).gauge_ball x]
        apply le_csInf hB.gauge_set_nonempty
        rintro b ⟨hb, y, hy, rfl⟩
        change ‖φ.val (b • y)‖ ≤ b
        have hmap : φ.val (b • y) = b • φ.val y := φ.val.toLinearMap.map_smul_of_tower b y
        rw [hmap, norm_smul, Real.norm_of_nonneg hb.le]
        exact mul_le_of_le_one_right hb.le ((StrongDual.mem_polar_iff ℂ _).mp φ.property y (hpU hy))
      have hφ (x : E) : ‖φ.val x‖ ≤ D * ‖aL x‖ := (hpφ x).trans (ha x)
      let g := φ.val.toLinearMap.extendOfNorm (σ₁₂ := RingHom.id ℂ) aL
      let ψ := g.comp L.orthogonalProjectionOnto
      refine ⟨⟨ψ, (StrongDual.mem_polar_iff ℂ _).mpr fun w hw ↦ ?_⟩, ?_⟩
      · have hw' : ‖w‖ < (D + 1)⁻¹ := mem_ball_zero_iff.mp hw
        change ‖g (L.orthogonalProjectionOnto w)‖ ≤ 1
        calc
          _ ≤ D * ‖L.orthogonalProjectionOnto w‖ :=
            LinearMap.norm_extendOfNorm_apply_le hd D hφ _
          _ ≤ (D + 1) * ‖w‖ :=
            mul_le_mul (le_add_of_nonneg_right zero_le_one)
              (L.norm_orthogonalProjectionOnto_apply_le w) (norm_nonneg _) (by positivity)
          _ ≤ 1 := (mul_le_mul_of_nonneg_left hw'.le (by positivity)).trans_eq
            (mul_inv_cancel₀ (by positivity : D + 1 ≠ 0))
      · ext x
        change g (L.orthogonalProjectionOnto (a x)) = φ.val x
        rw [show L.orthogonalProjectionOnto (a x) = aL x from
          L.orthogonalProjectionOnto_mem_subspace_eq_self (aL x)]
        exact LinearMap.extendOfNorm_eq hd ⟨D, hφ⟩ x
    have hA (z : E ⊗[ℂ] F) : injectiveTensorSeminorm U V z ≤
        injectiveTensorSeminorm W V (TensorProduct.map a.toLinearMap LinearMap.id z) := by
      obtain ⟨hBdd, hSup⟩ :=
        injectiveSeminorm_eq_ciSup W V (TensorProduct.map a.toLinearMap LinearMap.id z)
      rw [(injectiveSeminorm_eq_ciSup U V z).2, hSup]
      have : Nonempty (StrongDual.polar ℂ U.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
      have : Nonempty (StrongDual.polar ℂ V.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
      apply ciSup_le
      rintro ⟨φ, η⟩
      obtain ⟨ψ, hψ⟩ := hfactor φ
      have heq : (tensorDualForm ψ.val η.val).comp (TensorProduct.map a.toLinearMap LinearMap.id) =
          tensorDualForm φ.val η.val := by
        apply TensorProduct.ext'
        intro x y
        have hx : ψ.val (a x) = φ.val x := DFunLike.congr_fun hψ x
        simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
          tensorDualForm_tmul, ContinuousLinearMap.coe_coe, hx]
      rw [← DFunLike.congr_fun heq z]
      exact le_ciSup hBdd (ψ, η)
    let K := (S.map a.toLinearMap).topologicalClosure
    let : CompleteSpace K := (S.map a.toLinearMap).isClosed_topologicalClosure.completeSpace_coe
    let a' := Kᗮ.starProjection.comp a
    have hker : S ≤ a'.ker := fun x hx ↦
      K.starProjection_orthogonal_apply_eq_zero
        (Submodule.le_topologicalClosure _ ⟨x, hx, rfl⟩)
    let b : Q →L[ℂ] H := S.liftQL a' hker
    let M := injectiveTensorMap b.toLinearMap (ContinuousLinearMap.id ℂ F).toLinearMap
    have hM : Continuous M := injectiveTensorMap_continuous b (ContinuousLinearMap.id ℂ F)
    have hMT : M.comp T = TensorProduct.map a'.toLinearMap LinearMap.id := by
      apply TensorProduct.ext'
      intro x y
      change TensorProduct.map b.toLinearMap LinearMap.id
        (TensorProduct.map S.mkQ LinearMap.id (x ⊗ₜ[ℂ] y)) =
          TensorProduct.map a'.toLinearMap LinearMap.id (x ⊗ₜ[ℂ] y)
      simp only [TensorProduct.map_tmul, LinearMap.id_apply]
      rfl
    let s : Seminorm ℂ (InjectiveTensor Q F) := (injectiveTensorSeminorm W V).comp M
    refine Seminorm.continuous_of_le (q := C • s)
      (((withGeneratingSeminorms_spec (H ⊗[ℂ] F) _).continuous_seminorm (W, V)).comp hM
        |>.const_smul C) fun z ↦ ?_
    have hT : Function.Surjective T :=
      TensorProduct.map_surjective S.mkQ_surjective (show Function.Surjective
        (LinearMap.id : F →ₗ[ℂ] F) from Function.surjective_id)
    obtain ⟨z, rfl⟩ := hT z
    change r (T z) ≤ (C : ℝ) * injectiveTensorSeminorm W V (M (T z))
    rw [show M (T z) = TensorProduct.map a'.toLinearMap LinearMap.id z from
      DFunLike.congr_fun hMT z]
    exact quotientTensorSeminorm_le_projection S a.toLinearMap r W V C
      (fun z ↦ (hC z).trans (mul_le_mul_of_nonneg_left (hA z) C.coe_nonneg)) z
  exact (⟨Equiv.refl (Q ⊗[ℂ] F), (uniformContinuous_tensorComparison Q F).continuous, hback⟩ :
    ProjectiveTensor Q F ≃ₜ InjectiveTensor Q F).isHomeomorph

/-- Paper: Lemma C.2.4.10(2), p. 689. A product of nuclear spaces is nuclear for
the product topology. -/
theorem isNuclearTVS_pi {I : Type w} {X : I → Type u}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    (hX : ∀ i, IsNuclearTVS.{max v w, u} (X i)) : IsNuclearTVS.{v, max u w} (∀ i, X i) := by
  classical
  let : ∀ i, T2Space (X i) := fun i ↦ (hX i).1
  let : ∀ i, PolynormableSpace ℂ (X i) := fun i ↦ (hX i).2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro F _ _ _ _ _
  let proj (i : I) : (∀ i, X i) →L[ℂ] X i := ContinuousLinearMap.proj i
  let single (i : I) := ContinuousLinearMap.single ℂ X i
  let M (i : I) : ((∀ i, X i) ⊗[ℂ] F) →ₗ[ℂ] ((∀ i, X i) ⊗[ℂ] F) :=
    ((single i).toLinearMap.rTensor F).comp ((proj i).toLinearMap.rTensor F)
  have hM (i : I) : Continuous
      (show InjectiveTensor (∀ i, X i) F → ProjectiveTensor (∀ i, X i) F from M i) := by
    let e := ((hX i).2.2 F inferInstance inferInstance inferInstance inferInstance
      inferInstance).homeomorph
    have hback : Continuous (show InjectiveTensor (X i) F → ProjectiveTensor (X i) F from id) :=
      e.continuous_symm.congr fun z ↦ e.apply_symm_apply z
    exact ((projectiveTensorMap_continuous (single i) (ContinuousLinearMap.id ℂ F)).comp
      hback).comp (injectiveTensorMap_continuous (proj i) (ContinuousLinearMap.id ℂ F))
  let hP := withGeneratingSeminorms_spec ((∀ i, X i) ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ ((∀ i, X i) ⊗[ℂ] F) // ContinuousAt
        (fun z : (∀ i, X i) × F ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
  have hback : Continuous (show InjectiveTensor (∀ i, X i) F →
      ProjectiveTensor (∀ i, X i) F from id) := by
    refine hP.continuous_of_continuous_comp
      (LinearMap.id : InjectiveTensor (∀ i, X i) F →ₗ[ℂ] ProjectiveTensor (∀ i, X i) F)
      fun ⟨r, hr⟩ ↦ ?_
    obtain ⟨q, p, hq, _, hbound⟩ := exists_projectiveSeminorm_pure_bound (∀ i, X i) r hr
    -- The seminorm bounding the first factor depends on finitely many coordinates.
    obtain ⟨s, C, _, hs⟩ := Seminorm.bound_of_continuous
      (withSeminorms_pi (fun i ↦ PolynormableSpace.withSeminorms ℂ (X i))) q hq
    let t := s.image Sigma.fst
    have hqzero (x : ∀ i, X i) (hx : ∀ i ∈ t, x i = 0) : q x = 0 := by
      apply le_antisymm ?_ (apply_nonneg q x)
      refine (hs x).trans ?_
      rw [smul_apply, ← smul_zero C]
      refine smul_le_smul_of_nonneg_left (Seminorm.finset_sup_apply_le (le_refl 0) ?_) zero_le
      intro j hj
      change j.2.val (x j.1) ≤ 0
      rw [hx _ (Finset.mem_image_of_mem _ hj), map_zero]
    let T := ∑ i ∈ t, M i
    have hT : Continuous
        (show InjectiveTensor (∀ i, X i) F → ProjectiveTensor (∀ i, X i) F from T) :=
      (continuous_finsetSum t (fun i _ ↦ hM i)).congr fun z ↦
        (LinearMap.sum_apply t M z).symm
    let D := LinearMap.id - T
    have hD (z : (∀ i, X i) ⊗[ℂ] F) : r (D z) = 0 := by
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
        change r (x ⊗ₜ[ℂ] y - T (x ⊗ₜ[ℂ] y)) = 0
        simp only [T, M, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul]
        rw [← sum_tmul, ← sub_tmul]
        apply le_antisymm ((hbound _ y).trans_eq ?_) (apply_nonneg _ _)
        rw [hqzero, zero_mul]
        intro i hi
        rw [Pi.sub_apply, Finset.sum_apply, Finset.sum_eq_single_of_mem i hi]
        · simp [single, proj]
        · intro j _ hji
          exact Pi.single_eq_of_ne hji.symm _
      | add z z' hz hz' =>
        rw [map_add]
        exact le_antisymm ((map_add_le_add r _ _).trans_eq (by rw [hz, hz', add_zero]))
          (apply_nonneg _ _)
    let rT : Seminorm ℂ (InjectiveTensor (∀ i, X i) F) := r.comp T
    refine Seminorm.continuous_of_le (q := rT)
      ((hP.continuous_seminorm ⟨r, hr⟩).comp hT) fun z ↦ ?_
    change r z ≤ r (T z)
    have h := map_add_le_add r (D z) (T z)
    rwa [hD z, zero_add, show D z + T z = z from sub_add_cancel z (T z)] at h
  exact (⟨Equiv.refl ((∀ i, X i) ⊗[ℂ] F), (uniformContinuous_tensorComparison _ F).continuous,
    hback⟩ : ProjectiveTensor (∀ i, X i) F ≃ₜ InjectiveTensor (∀ i, X i) F).isHomeomorph

/-- A partial geometric series of ratio one half is at most two. -/
private theorem sum_half_geometric (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i = 2 * (1 - (1 / 2) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Countable weights `2 ^ {-e i}` sum to at most two when `e` is injective. -/
private theorem sum_pow_half_injective_le_two {ι : Type*} (e : ι → ℕ) (he : Function.Injective e)
    (s : Finset ι) : ∑ i ∈ s, (1 / 2 : ℝ) ^ e i ≤ 2 := by
  by_cases hs : s = ∅
  · simp [hs]
  · have hsn : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
    have himg : (s.image e).Nonempty := hsn.image _
    let M := (s.image e).max' himg
    have hsub : s.image e ⊆ Finset.range (M + 1) := by
      intro n hn
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le ((s.image e).le_max' _ hn)
    calc
      ∑ i ∈ s, (1 / 2 : ℝ) ^ e i = ∑ n ∈ s.image e, (1 / 2 : ℝ) ^ n := by
        rw [Finset.sum_image (f := fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) he.injOn]
      _ ≤ ∑ n ∈ Finset.range (M + 1), (1 / 2 : ℝ) ^ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
      _ = 2 * (1 - (1 / 2 : ℝ) ^ (M + 1)) := sum_half_geometric (M + 1)
      _ ≤ 2 := by
        have : 0 ≤ (1 / 2 : ℝ) ^ (M + 1) := by positivity
        linarith

private theorem tensorDualForm_smul_left_apply {G H : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]
    (φ : StrongDual ℂ G) (ψ : StrongDual ℂ H) (c : ℂ) (z : G ⊗[ℂ] H) :
    tensorDualForm (c • φ) ψ z = c * tensorDualForm φ ψ z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [tensorDualForm_tmul, tensorDualForm_tmul, smul_apply, smul_eq_mul, mul_assoc]
  | add z w hz hw =>
    rw [map_add, map_add, hz, hw, mul_add]

private theorem tensorDualForm_smul_right {G H : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]
    (φ : StrongDual ℂ G) (ψ : StrongDual ℂ H) (c : ℂ) (z : G ⊗[ℂ] H) :
    tensorDualForm φ (c • ψ) z = c * tensorDualForm φ ψ z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [tensorDualForm_tmul, tensorDualForm_tmul, smul_apply, smul_eq_mul]
    ring
  | add z w hz hw =>
    rw [map_add, map_add, hz, hw, mul_add]

private theorem tensorDualForm_comp_rTensor {G X H : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]
    (f : G →L[ℂ] X) (φ : StrongDual ℂ X) (ψ : StrongDual ℂ H) (z : G ⊗[ℂ] H) :
    tensorDualForm (φ.comp f) ψ z = tensorDualForm φ ψ (f.toLinearMap.rTensor H z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp [tensorDualForm_tmul, LinearMap.rTensor_tmul]
  | add z w hz hw =>
    simp [map_add, hz, hw]

private theorem directSumLeft_apply_component {ι : Type*} [DecidableEq ι] {X : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] {H : Type*} [AddCommGroup H] [Module ℂ H]
    (z : (⨁ i, X i) ⊗[ℂ] H) (i : ι) :
    (TensorProduct.directSumLeft ℂ ℂ X H z) i =
      (DirectSum.component ℂ ι X i).rTensor H z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.directSumLeft_tmul, LinearMap.rTensor_tmul, ← DirectSum.apply_eq_component]
  | add z w hz hw =>
    rw [map_add, map_add, DFinsupp.add_apply, hz, hw]

private theorem continuous_nnreal_smul_seminorm {G : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (p : Seminorm ℂ G) (hp : Continuous p) (c : NNReal) :
    Continuous (⇑(c • p)) := by
  have hfun : ⇑(c • p) = fun x ↦ (c : ℝ) * p x := by
    funext x
    rw [smul_apply, NNReal.smul_def, smul_eq_mul]
  rw [hfun]
  exact continuous_const.mul hp

/-- Shrinking either polar neighborhood increases the injective seminorm. -/
private theorem injectiveTensorSeminorm_antitone {G H : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] [PolynormableSpace ℂ G] [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]
    [PolynormableSpace ℂ H] {U₁ U₂ : {U : Set G // U ∈ 𝓝 0}} {V₁ V₂ : {V : Set H // V ∈ 𝓝 0}}
    (hU : U₂.val ⊆ U₁.val) (hV : V₂.val ⊆ V₁.val) (z : G ⊗[ℂ] H) :
    injectiveTensorSeminorm U₁ V₁ z ≤ injectiveTensorSeminorm U₂ V₂ z := by
  obtain ⟨-, hsup1⟩ := injectiveSeminorm_eq_ciSup U₁ V₁ z
  obtain ⟨hb2, hsup2⟩ := injectiveSeminorm_eq_ciSup U₂ V₂ z
  rw [hsup1, hsup2]
  have : Nonempty (StrongDual.polar ℂ U₁.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  have : Nonempty (StrongDual.polar ℂ V₁.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  apply ciSup_le
  rintro ⟨φ, ψ⟩
  have hφ : φ.val ∈ StrongDual.polar ℂ U₂.val :=
    (StrongDual.mem_polar_iff ℂ _).mpr fun x hx ↦
      (StrongDual.mem_polar_iff ℂ _).mp φ.property x (hU hx)
  have hψ : ψ.val ∈ StrongDual.polar ℂ V₂.val :=
    (StrongDual.mem_polar_iff ℂ _).mpr fun y hy ↦
      (StrongDual.mem_polar_iff ℂ _).mp ψ.property y (hV hy)
  exact le_ciSup hb2 (⟨φ.val, hφ⟩, ⟨ψ.val, hψ⟩)

private theorem norm_ofReal_eq (t : ℝ) (ht : 0 ≤ t) : ‖(t : ℂ)‖ = t := by
  rw [Complex.norm_real, Real.norm_of_nonneg ht]

/-- Rescaling the closed ball in a normed factor rescales the injective seminorm. -/
private theorem injectiveTensorSeminorm_closedBall_radius {G H : Type*} [AddCommGroup G]
    [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G] [NormedAddCommGroup H]
    [NormedSpace ℂ H] (U : {U : Set G // U ∈ 𝓝 0}) {t : ℝ} (ht : 0 < t) (z : G ⊗[ℂ] H) :
    injectiveTensorSeminorm U ⟨Metric.closedBall (0 : H) t, Metric.closedBall_mem_nhds 0 ht⟩ z =
      t⁻¹ * injectiveTensorSeminorm U
        ⟨Metric.closedBall (0 : H) 1, Metric.closedBall_mem_nhds 0 one_pos⟩ z := by
  let Vt : {V : Set H // V ∈ 𝓝 0} := ⟨Metric.closedBall 0 t, Metric.closedBall_mem_nhds 0 ht⟩
  let V1 : {V : Set H // V ∈ 𝓝 0} := ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩
  obtain ⟨hbt, hsupt⟩ := injectiveSeminorm_eq_ciSup U Vt z
  obtain ⟨hb1, hsup1⟩ := injectiveSeminorm_eq_ciSup U V1 z
  rw [hsupt, hsup1]
  have : Nonempty (StrongDual.polar ℂ U.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  have : Nonempty (StrongDual.polar ℂ Vt.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  have : Nonempty (StrongDual.polar ℂ V1.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  apply le_antisymm
  · apply ciSup_le
    rintro ⟨φ, ψ⟩
    let ψ1 : StrongDual ℂ H := (t : ℂ) • ψ.val
    have hψ1 : ψ1 ∈ StrongDual.polar ℂ V1.val := by
      rw [StrongDual.mem_polar_iff]
      intro y hy
      rw [Metric.mem_closedBall, dist_zero_right] at hy
      have hmem : (t : ℂ) • y ∈ Vt.val := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_ofReal_eq t ht.le, mul_comm]
        exact mul_le_of_le_one_left ht.le hy
      have hψ := (StrongDual.mem_polar_iff ℂ _).mp ψ.property _ hmem
      rw [map_smul, smul_eq_mul, norm_mul, norm_ofReal_eq t ht.le] at hψ
      change ‖ψ1 y‖ ≤ 1
      rwa [show ψ1 y = (t : ℂ) * ψ.val y by rw [smul_apply, smul_eq_mul], norm_mul,
        norm_ofReal_eq t ht.le]
    have hψeq : ψ.val = ((t : ℂ)⁻¹) • ψ1 := by
      unfold ψ1
      rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast ht.ne'), one_smul]
    rw [show ‖tensorDualForm φ.val ψ.val z‖ = t⁻¹ * ‖tensorDualForm φ.val ψ1 z‖ by
      rw [hψeq, tensorDualForm_smul_right, norm_mul, norm_inv, norm_ofReal_eq t ht.le]]
    exact mul_le_mul_of_nonneg_left (le_ciSup hb1 (⟨φ, ⟨ψ1, hψ1⟩⟩)) (inv_nonneg.mpr ht.le)
  · rw [inv_mul_le_iff₀ ht]
    apply ciSup_le
    rintro ⟨φ, ψ⟩
    let ψt : StrongDual ℂ H := ((t : ℂ)⁻¹) • ψ.val
    have hψt : ψt ∈ StrongDual.polar ℂ Vt.val := by
      rw [StrongDual.mem_polar_iff]
      intro y hy
      rw [Metric.mem_closedBall, dist_zero_right] at hy
      have hmem : ((t : ℂ)⁻¹) • y ∈ V1.val := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_ofReal_eq t ht.le]
        rw [inv_mul_le_iff₀ ht, mul_one]
        exact hy
      have hψ := (StrongDual.mem_polar_iff ℂ _).mp ψ.property _ hmem
      rw [map_smul, smul_eq_mul, norm_mul, norm_inv, norm_ofReal_eq t ht.le] at hψ
      change ‖ψt y‖ ≤ 1
      rwa [show ψt y = (t : ℂ)⁻¹ * ψ.val y by rw [smul_apply, smul_eq_mul], norm_mul, norm_inv,
        norm_ofReal_eq t ht.le]
    have hψeq : ψ.val = (t : ℂ) • ψt := by
      unfold ψt
      rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast ht.ne'), one_smul]
    rw [show ‖tensorDualForm φ.val ψ.val z‖ = t * ‖tensorDualForm φ.val ψt z‖ by
      rw [hψeq, tensorDualForm_smul_right, norm_mul, norm_ofReal_eq t ht.le]]
    exact mul_le_mul_of_nonneg_left (le_ciSup hbt (⟨φ, ⟨ψt, hψt⟩⟩)) ht.le

/-- Scaling a seminorm ball on the first factor scales the injective seminorm. -/
private theorem injectiveTensorSeminorm_smul_ball {G H : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] [PolynormableSpace ℂ G] [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]
    [PolynormableSpace ℂ H] (p : Seminorm ℂ G) (hp : Continuous p) {c : NNReal} (hc : 0 < c)
    (V : {V : Set H // V ∈ 𝓝 0}) (z : G ⊗[ℂ] H) :
    injectiveTensorSeminorm ⟨(c • p).ball 0 1,
        (c • p).ball_mem_nhds (continuous_nnreal_smul_seminorm p hp c) one_pos⟩ V z =
      (c : ℝ) * injectiveTensorSeminorm ⟨p.ball 0 1, p.ball_mem_nhds hp one_pos⟩ V z := by
  let pc : {U : Set G // U ∈ 𝓝 0} := ⟨(c • p).ball 0 1,
    (c • p).ball_mem_nhds (continuous_nnreal_smul_seminorm p hp c) one_pos⟩
  let p1 : {U : Set G // U ∈ 𝓝 0} := ⟨p.ball 0 1, p.ball_mem_nhds hp one_pos⟩
  obtain ⟨hbc, hsupc⟩ := injectiveSeminorm_eq_ciSup pc V z
  obtain ⟨hb1, hsup1⟩ := injectiveSeminorm_eq_ciSup p1 V z
  rw [hsupc, hsup1]
  have : Nonempty (StrongDual.polar ℂ pc.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  have : Nonempty (StrongDual.polar ℂ p1.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  have : Nonempty (StrongDual.polar ℂ V.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (NNReal.coe_pos.mpr hc).ne'
  have hcnorm : ‖(c : ℂ)‖ = (c : ℝ) := norm_ofReal_eq (c : ℝ) c.coe_nonneg
  apply le_antisymm
  · apply ciSup_le
    rintro ⟨φ, ψ⟩
    let η : StrongDual ℂ G := ((c : ℂ)⁻¹) • φ.val
    have hη : η ∈ StrongDual.polar ℂ p1.val := by
      rw [StrongDual.mem_polar_iff]
      intro x hx
      rw [Seminorm.mem_ball_zero] at hx
      have hmem : ((c : ℂ)⁻¹) • x ∈ pc.val := by
        rw [Seminorm.mem_ball_zero, smul_apply, NNReal.smul_def, smul_eq_mul, map_smul_eq_mul,
          norm_inv, hcnorm, ← mul_assoc, mul_inv_cancel₀ (NNReal.coe_pos.mpr hc).ne', one_mul]
        exact hx
      have hφ := (StrongDual.mem_polar_iff ℂ _).mp φ.property _ hmem
      rw [map_smul, smul_eq_mul, norm_mul, norm_inv, hcnorm] at hφ
      change ‖η x‖ ≤ 1
      rwa [show η x = (c : ℂ)⁻¹ * φ.val x by rw [smul_apply, smul_eq_mul], norm_mul, norm_inv, hcnorm]
    have hφeq : φ.val = (c : ℂ) • η := by
      unfold η
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    rw [show ‖tensorDualForm φ.val ψ.val z‖ = (c : ℝ) * ‖tensorDualForm η ψ.val z‖ by
      rw [hφeq, tensorDualForm_smul_left_apply, norm_mul, hcnorm]]
    exact mul_le_mul_of_nonneg_left (le_ciSup hb1 (⟨η, hη⟩, ψ)) c.coe_nonneg
  · rw [← le_inv_mul_iff₀ (NNReal.coe_pos.mpr hc)]
    apply ciSup_le
    rintro ⟨φ, ψ⟩
    let θ : StrongDual ℂ G := (c : ℂ) • φ.val
    have hθ : θ ∈ StrongDual.polar ℂ pc.val := by
      rw [StrongDual.mem_polar_iff]
      intro x hx
      rw [Seminorm.mem_ball_zero, smul_apply, NNReal.smul_def, smul_eq_mul] at hx
      have hmem : (c : ℂ) • x ∈ p1.val := by
        rw [Seminorm.mem_ball_zero, map_smul_eq_mul, hcnorm]
        exact hx
      have hφ := (StrongDual.mem_polar_iff ℂ _).mp φ.property _ hmem
      rw [map_smul, smul_eq_mul, norm_mul, hcnorm] at hφ
      change ‖θ x‖ ≤ 1
      rwa [show θ x = (c : ℂ) * φ.val x by rw [smul_apply, smul_eq_mul], norm_mul, hcnorm]
    have hφeq : φ.val = ((c : ℂ)⁻¹) • θ := by
      unfold θ
      rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [show ‖tensorDualForm φ.val ψ.val z‖ = (c : ℝ)⁻¹ * ‖tensorDualForm θ ψ.val z‖ by
      rw [hφeq, tensorDualForm_smul_left_apply, norm_mul, norm_inv, hcnorm]]
    exact mul_le_mul_of_nonneg_left (le_ciSup hbc (⟨θ, hθ⟩, ψ)) (inv_nonneg.mpr c.coe_nonneg)

/-- A continuous seminorm on an injective tensor with a normed factor is bounded by one
injective seminorm tested on the closed unit ball. -/
private theorem exists_injectiveTensorSeminorm_unitBall {G H : Type*} [AddCommGroup G]
    [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G] [NormedAddCommGroup H]
    [NormedSpace ℂ H] (s : Seminorm ℂ (G ⊗[ℂ] H))
    (hs : Continuous (show InjectiveTensor G H → ℝ from s)) :
    ∃ (p : Seminorm ℂ G) (hp : Continuous p) (C : NNReal), 0 < C ∧
      ∀ z, s z ≤ (C : ℝ) * injectiveTensorSeminorm ⟨p.ball 0 1, p.ball_mem_nhds hp one_pos⟩
        ⟨Metric.closedBall (0 : H) 1, Metric.closedBall_mem_nhds 0 one_pos⟩ z := by
  have : PolynormableSpace ℂ H := (norm_withSeminorms ℂ H).toPolynormableSpace
  let hI := withGeneratingSeminorms_spec (G ⊗[ℂ] H)
    (fun UV : {U : Set G // U ∈ 𝓝 0} × {V : Set H // V ∈ 𝓝 0} ↦ injectiveTensorSeminorm UV.1 UV.2)
  obtain ⟨S, C, hCne, hC⟩ := Seminorm.bound_of_continuous hI s hs
  let Uset : Set G := ⋂ UV ∈ S, (UV.1.val : Set G)
  let Vset : Set H := ⋂ UV ∈ S, (UV.2.val : Set H)
  have hUset : Uset ∈ 𝓝 0 := S.iInter_mem_sets.mpr fun UV _ ↦ UV.1.property
  have hVset : Vset ∈ 𝓝 0 := S.iInter_mem_sets.mpr fun UV _ ↦ UV.2.property
  let U : {U : Set G // U ∈ 𝓝 0} := ⟨Uset, hUset⟩
  let V : {V : Set H // V ∈ 𝓝 0} := ⟨Vset, hVset⟩
  have hsuple (z : G ⊗[ℂ] H) :
      (S.sup fun UV ↦ injectiveTensorSeminorm UV.1 UV.2) z ≤ injectiveTensorSeminorm U V z := by
    have hmono : S.sup (fun UV ↦ injectiveTensorSeminorm UV.1 UV.2) ≤ injectiveTensorSeminorm U V := by
      refine Finset.sup_le fun UV hUV ↦ Seminorm.le_def.mpr fun w ↦ ?_
      exact injectiveTensorSeminorm_antitone
        (U₁ := UV.1) (U₂ := U) (V₁ := UV.2) (V₂ := V)
        (fun x hx ↦ (mem_iInter₂.mp hx) UV hUV)
        (fun y hy ↦ (mem_iInter₂.mp hy) UV hUV) w
    exact hmono z
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hVset
  let t : ℝ := r / 2
  have ht : 0 < t := half_pos hr
  have hball : Metric.closedBall (0 : H) t ⊆ Vset := by
    intro y hy
    apply hrV
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    exact hy.trans_lt (half_lt_self hr)
  let Vt : {V : Set H // V ∈ 𝓝 0} := ⟨Metric.closedBall 0 t, Metric.closedBall_mem_nhds 0 ht⟩
  let V1 : {V : Set H // V ∈ 𝓝 0} := ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩
  obtain ⟨p, hp, hpU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ G).mem_iff.mp hUset
  let Up : {U : Set G // U ∈ 𝓝 0} := ⟨p.ball 0 1, p.ball_mem_nhds hp one_pos⟩
  have hCpos : 0 < (C : ℝ) :=
    lt_of_le_of_ne C.coe_nonneg (Ne.symm (NNReal.coe_ne_zero.mpr hCne))
  refine ⟨p, hp, ⟨(C : ℝ) / t, div_nonneg C.coe_nonneg ht.le⟩, div_pos hCpos ht, fun z ↦ ?_⟩
  calc
    s z ≤ (C • S.sup fun UV ↦ injectiveTensorSeminorm UV.1 UV.2) z := hC z
    _ = (C : ℝ) * (S.sup fun UV ↦ injectiveTensorSeminorm UV.1 UV.2) z := by
      rw [smul_apply, NNReal.smul_def, smul_eq_mul]
    _ ≤ (C : ℝ) * injectiveTensorSeminorm U V z :=
      mul_le_mul_of_nonneg_left (hsuple z) C.coe_nonneg
    _ ≤ (C : ℝ) * injectiveTensorSeminorm U Vt z :=
      mul_le_mul_of_nonneg_left
        (injectiveTensorSeminorm_antitone (U₁ := U) (U₂ := U) (V₁ := V) (V₂ := Vt)
          subset_rfl hball z) C.coe_nonneg
    _ = (C : ℝ) * (t⁻¹ * injectiveTensorSeminorm U V1 z) := by
      rw [injectiveTensorSeminorm_closedBall_radius U ht z]
    _ ≤ (C : ℝ) * (t⁻¹ * injectiveTensorSeminorm Up V1 z) := by
      gcongr
      exact injectiveTensorSeminorm_antitone (U₁ := U) (U₂ := Up) (V₁ := V1) (V₂ := V1) hpU
        subset_rfl z
    _ = ((C : ℝ) / t) * injectiveTensorSeminorm Up V1 z := by ring

/-- Paper: Lemma C.2.4.10(2), p. 689. The locally convex direct sum of a countable
family of nuclear spaces is nuclear. -/
theorem isNuclearTVS_directSum {I : Type w} [Countable I] [DecidableEq I] {X : I → Type u}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    (hX : ∀ i, IsNuclearTVS.{max v w, u} (X i)) :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I X)
    IsNuclearTVS.{v, max u w} (⨁ i, X i) := by
  classical
  let E := ⨁ i, X i
  let lof := DirectSum.lof ℂ I X
  let : TopologicalSpace E := locallyConvexFinalTopology lof
  have : ∀ i, PolynormableSpace ℂ (X i) := fun i ↦ (hX i).2.1
  have : ∀ i, T2Space (X i) := fun i ↦ (hX i).1
  have hEs : WithSeminorms (E := E)
      (Subtype.val : {p : Seminorm ℂ E // ∀ i, Continuous (p ∘ lof i)} → Seminorm ℂ E) := ⟨rfl⟩
  let : PolynormableSpace ℂ E := hEs.toPolynormableSpace
  have : IsTopologicalAddGroup E := hEs.isTopologicalAddGroup
  have hcomp (i : I) : Continuous (DirectSum.component ℂ I X i : E → X i) := by
    have : IsTopologicalAddGroup (X i) :=
      (PolynormableSpace.withSeminorms ℂ (X i)).isTopologicalAddGroup
    refine (PolynormableSpace.withSeminorms ℂ (X i)).continuous_of_continuous_comp
      (DirectSum.component ℂ I X i) fun ⟨p, hp⟩ ↦ ?_
    refine hEs.continuous_seminorm ⟨p.comp (DirectSum.component ℂ I X i), fun j ↦ ?_⟩
    by_cases hij : i = j
    · subst hij
      have hfun : (fun x : X i ↦ (p.comp (DirectSum.component ℂ I X i)) (lof i x)) = fun x ↦ p x := by
        funext x
        simp [Seminorm.comp_apply, lof, DirectSum.component.lof_self]
      change Continuous (fun x : X i ↦ (p.comp (DirectSum.component ℂ I X i)) (lof i x))
      rw [hfun]
      exact hp
    · have hfun : (fun x : X j ↦ (p.comp (DirectSum.component ℂ I X i)) (lof j x)) = fun _ ↦ 0 := by
        funext x
        simp [Seminorm.comp_apply, lof, DirectSum.component.of, Ne.symm hij, map_zero]
      change Continuous (fun x : X j ↦ (p.comp (DirectSum.component ℂ I X i)) (lof j x))
      rw [hfun]
      exact continuous_const
  have : T2Space E := by
    refine T2Space.of_injective_continuous (f := fun x : E ↦ fun i ↦ x i) ?_ ?_
    · intro x y hxy
      ext i
      exact congrFun hxy i
    · exact continuous_pi fun i ↦
        (hcomp i).congr fun x ↦ (DirectSum.apply_eq_component (R := ℂ) x i).symm
  refine (isNuclearTVS_iff_completedTensor_banach (E := E)).mpr ?_
  intro F _ _ _
  have : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  refine (isHomeomorph_completedTensorComparison_iff E F).mpr ?_
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
      ContinuousAt (fun v : E × F ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val)
  have hfwd : Continuous (show ProjectiveTensor E F → InjectiveTensor E F from id) :=
    (uniformContinuous_tensorComparison E F).continuous
  have hback : Continuous (show InjectiveTensor E F → ProjectiveTensor E F from id) := by
    refine hP.continuous_of_continuous_comp
      (LinearMap.id : InjectiveTensor E F →ₗ[ℂ] ProjectiveTensor E F) fun ⟨r, hr⟩ ↦ ?_
    obtain ⟨e, he⟩ := Countable.exists_injective_nat I
    let D := ⨁ i, ProjectiveTensor (X i) F
    let lofY := DirectSum.lof ℂ I (fun i ↦ ProjectiveTensor (X i) F)
    let : TopologicalSpace D := locallyConvexFinalTopology lofY
    let : TopologicalSpace (⨁ i, X i ⊗[ℂ] F) := locallyConvexFinalTopology lofY
    let : TopologicalSpace ((⨁ i, X i) ⊗[ℂ] F) :=
      inferInstanceAs (TopologicalSpace (ProjectiveTensor (⨁ i, X i) F))
    have hD : WithSeminorms (E := D)
        (Subtype.val : {p : Seminorm ℂ D // ∀ i, Continuous (p ∘ lofY i)} → Seminorm ℂ D) := ⟨rfl⟩
    have hrcont : Continuous (show ProjectiveTensor E F → ℝ from r) := hP.continuous_seminorm ⟨r, hr⟩
    let α := TensorProduct.directSumLeft ℂ ℂ X F
    let q : Seminorm ℂ D := r.comp α.symm.toLinearMap
    have hq : Continuous (show D → ℝ from q) := by
      let hmap := (projectiveTensor_directSum X F).homeomorph
      have hbase := hrcont.comp hmap.continuous
      refine hbase.congr fun d ↦ ?_
      have h := IsHomeomorph.homeomorph_apply
        ((TensorProduct.directSumLeft ℂ ℂ X F).symm) (projectiveTensor_directSum X F) d
      have hcoe : (hmap d : (⨁ i, X i) ⊗[ℂ] F) =
          (TensorProduct.directSumLeft ℂ ℂ X F).symm d := h
      apply congrArg (fun x : (⨁ i, X i) ⊗[ℂ] F ↦ r x) at hcoe
      calc
        (⇑r ∘ ⇑hmap) d = r (hmap d) := rfl
        _ = r ((TensorProduct.directSumLeft ℂ ℂ X F).symm d) := hcoe
        _ = q d := (Seminorm.comp_apply r
            (TensorProduct.directSumLeft ℂ ℂ X F).symm.toLinearMap d).symm
    have hlof (i : I) : Continuous (lofY i) :=
      hD.continuous_of_continuous_comp (lofY i) fun s ↦ s.property i
    let s (i : I) : Seminorm ℂ (X i ⊗[ℂ] F) := q.comp (DirectSum.lof ℂ I (fun i ↦ X i ⊗[ℂ] F) i)
    have hsε (i : I) : Continuous (show InjectiveTensor (X i) F → ℝ from (s i)) := by
      have hsπ : Continuous (show ProjectiveTensor (X i) F → ℝ from (s i)) := hq.comp (hlof i)
      let hhome := ((hX i).2.2 F inferInstance inferInstance inferInstance inferInstance
        inferInstance).homeomorph
      have hsym (z : InjectiveTensor (X i) F) : hhome.symm z = z := by
        have happ : hhome z = z := rfl
        rw [← happ]
        exact hhome.symm_apply_apply z
      exact hsπ.comp (hhome.symm.continuous.congr hsym)
    have hsb (i : I) := exists_injectiveTensorSeminorm_unitBall (s i) (hsε i)
    choose p hp C hCpos hsbound using hsb
    let ρ (i : I) : NNReal := (2 : NNReal) ^ e i * C i
    have hρ (i : I) : 0 < ρ i :=
      mul_pos (pow_pos (by norm_num : (0 : NNReal) < 2) (e i)) (hCpos i)
    let σ (i : I) : Seminorm ℂ (X i) := ρ i • p i
    have hσ (i : I) : Continuous (σ i) := continuous_nnreal_smul_seminorm (p i) (hp i) (ρ i)
    let qE : Seminorm ℂ E := directSumSeminorm σ
    have hqE : Continuous qE := by
      refine hEs.continuous_seminorm ⟨qE, fun i ↦ ?_⟩
      have hfun : (fun x : X i ↦ qE (lof i x)) = fun x ↦ σ i x := by
        funext x
        rw [directSumSeminorm_lof]
      change Continuous (fun x : X i ↦ qE (lof i x))
      rw [hfun]
      exact hσ i
    let UE : {U : Set E // U ∈ 𝓝 0} := ⟨qE.ball 0 1, qE.ball_mem_nhds hqE one_pos⟩
    let VF : {V : Set F // V ∈ 𝓝 0} :=
      ⟨Metric.closedBall (0 : F) 1, Metric.closedBall_mem_nhds 0 one_pos⟩
    let Uj (j : I) : {U : Set (X j) // U ∈ 𝓝 0} :=
      ⟨(ρ j • p j).ball 0 1, (ρ j • p j).ball_mem_nhds
        (continuous_nnreal_smul_seminorm (p j) (hp j) (ρ j)) one_pos⟩
    have hdom (j : I) (z : E ⊗[ℂ] F) :
        injectiveTensorSeminorm (Uj j) VF ((α z) j) ≤ injectiveTensorSeminorm UE VF z := by
      obtain ⟨-, hsupj⟩ := injectiveSeminorm_eq_ciSup (Uj j) VF ((α z) j)
      obtain ⟨hbE, hsupE⟩ := injectiveSeminorm_eq_ciSup UE VF z
      rw [hsupj, hsupE]
      have : Nonempty (StrongDual.polar ℂ (Uj j).val) := (StrongDual.polar_nonempty ℂ _).to_subtype
      have : Nonempty (StrongDual.polar ℂ VF.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
      apply ciSup_le
      rintro ⟨φ, ψ⟩
      let πj : E →L[ℂ] X j := ⟨DirectSum.component ℂ I X j, hcomp j⟩
      let Φ : StrongDual ℂ E := φ.val.comp πj
      have hΦ : Φ ∈ StrongDual.polar ℂ UE.val := by
        rw [StrongDual.mem_polar_iff]
        intro x hx
        rw [Seminorm.mem_ball_zero] at hx
        have hle : σ j (x j) ≤ qE x := by
          rw [← Finset.sum_singleton (fun i : I ↦ σ i (x i)) j]
          exact sum_le_directSumSeminorm σ x {j}
        have hxj : σ j (x j) < 1 := hle.trans_lt hx
        have hxball : x j ∈ (σ j).ball 0 1 := by
          rw [Seminorm.mem_ball_zero]
          exact hxj
        have hφ := (StrongDual.mem_polar_iff ℂ _).mp φ.property _ hxball
        change ‖Φ x‖ ≤ 1
        have hΦx : Φ x = φ.val (x j) := by
          change φ.val ((DirectSum.component ℂ I X j) x) = φ.val (x j)
          rw [← DirectSum.apply_eq_component (R := ℂ) x j]
        rw [hΦx]
        exact hφ
      have hform : tensorDualForm φ.val ψ.val ((α z) j) = tensorDualForm Φ ψ.val z := by
        rw [tensorDualForm_comp_rTensor πj φ.val ψ.val z]
        rw [← directSumLeft_apply_component]
      rw [hform]
      exact le_ciSup hbE (⟨Φ, hΦ⟩, ψ)
    have hscale (j : I) (w : X j ⊗[ℂ] F) :
        (s j) w ≤ (1 / 2 : ℝ) ^ e j * injectiveTensorSeminorm (Uj j) VF w := by
      have hsmul := injectiveTensorSeminorm_smul_ball (p j) (hp j) (hρ j) VF w
      have hcoe : (ρ j : ℝ) = (2 : ℝ) ^ e j * (C j : ℝ) := by
        simp [ρ, NNReal.coe_mul, NNReal.coe_pow]
      have hfactor : (C j : ℝ) = (1 / 2 : ℝ) ^ e j * (ρ j : ℝ) := by
        rw [hcoe, ← mul_assoc, ← mul_pow]
        norm_num
      calc
        (s j) w ≤ (C j : ℝ) * injectiveTensorSeminorm ⟨(p j).ball 0 1,
            (p j).ball_mem_nhds (hp j) one_pos⟩ VF w := hsbound j w
        _ = ((1 / 2 : ℝ) ^ e j * (ρ j : ℝ)) *
            injectiveTensorSeminorm ⟨(p j).ball 0 1, (p j).ball_mem_nhds (hp j) one_pos⟩ VF w := by
          rw [hfactor]
        _ = (1 / 2 : ℝ) ^ e j * injectiveTensorSeminorm (Uj j) VF w := by
          dsimp only [Uj]
          rw [mul_assoc, ← hsmul]
    have htri (z : E ⊗[ℂ] F) : r z ≤ ∑ j ∈ (α z).support, (s j) ((α z) j) := by
      have hrq : q (α z) = r z := by
        rw [show q (α z) = r (α.symm (α z)) from rfl, α.symm_apply_apply]
      rw [← hrq]
      let terms (j : I) := DirectSum.lof ℂ I (fun i ↦ ProjectiveTensor (X i) F) j ((α z) j)
      have hineq := Finset.le_sum_of_subadditive (⇑q) (map_zero q).le
        (fun a b ↦ map_add_le_add q a b) (α z).support terms
      have hsum : (∑ j ∈ (α z).support, terms j) = α z := DirectSum.sum_support_of (α z)
      rw [hsum] at hineq
      refine hineq.trans_eq ?_
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [terms, s]
      rfl
    have hfin (z : E ⊗[ℂ] F) : r z ≤ 2 * injectiveTensorSeminorm UE VF z := by
      calc
        r z ≤ ∑ j ∈ (α z).support, (s j) ((α z) j) := htri z
        _ ≤ ∑ j ∈ (α z).support, (1 / 2 : ℝ) ^ e j * injectiveTensorSeminorm UE VF z := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          exact (hscale j ((α z) j)).trans
            (mul_le_mul_of_nonneg_left (hdom j z) (by positivity))
        _ = (∑ j ∈ (α z).support, (1 / 2 : ℝ) ^ e j) * injectiveTensorSeminorm UE VF z := by
          rw [← Finset.sum_mul]
        _ ≤ 2 * injectiveTensorSeminorm UE VF z :=
          mul_le_mul_of_nonneg_right (sum_pow_half_injective_le_two e he (α z).support)
            (apply_nonneg _ _)
    let hI := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
      (fun UV : {U : Set E // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
        injectiveTensorSeminorm UV.1 UV.2)
    refine Seminorm.continuous_of_le
      (q := (2 : NNReal) • injectiveTensorSeminorm UE VF)
      ((hI.continuous_seminorm (UE, VF)).const_smul (2 : NNReal)) ?_
    intro z
    exact hfin z
  exact (⟨Equiv.refl (E ⊗[ℂ] F), hfwd, hback⟩ :
    ProjectiveTensor E F ≃ₜ InjectiveTensor E F).isHomeomorph


/-- The inverse associator is continuous for the iterated projective topologies.
A seminorm on the left gives a family of seminorms on the inner tensor on the right,
indexed by the closed unit ball of a seminorm on the first factor. -/
private theorem continuous_projectiveTensor_assoc_symm {F G : Type*}
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G]
    [PolynormableSpace ℂ E] :
    @Continuous (ProjectiveTensor E (ProjectiveTensor F G))
      (ProjectiveTensor (ProjectiveTensor E F) G) _ _ (TensorProduct.assoc ℂ E F G).symm := by
  let P := ProjectiveTensor E F
  let Q := ProjectiveTensor F G
  let A : ProjectiveTensor E Q →ₗ[ℂ] ProjectiveTensor P G :=
    (TensorProduct.assoc ℂ E F G).symm.toLinearMap
  change Continuous A
  refine (withGeneratingSeminorms_spec (P ⊗[ℂ] G) _).continuous_of_continuous_comp A
    fun ⟨p, hp⟩ ↦ ?_
  obtain ⟨q, s, hq, hs, hpqs⟩ := exists_projectiveSeminorm_pure_bound P p hp
  obtain ⟨a, b, ha, hb, hqab⟩ := exists_projectiveSeminorm_pure_bound E q (by
    have ht : @ContinuousAt (E × F) P _ _ (fun v ↦ v.1 ⊗ₜ[ℂ] v.2) 0 := by
      let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
        (fun r : {r : Seminorm ℂ (E ⊗[ℂ] F) //
          ContinuousAt (fun v : E × F ↦ r (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ r.val)
      let tmul : E × F → P := fun v ↦ v.1 ⊗ₜ[ℂ] v.2
      have hzero : tmul 0 = 0 := zero_tmul _ _
      change Tendsto tmul (𝓝 0) (𝓝 (tmul 0))
      rw [hzero, (SeminormFamily.withSeminorms_iff_nhds_eq_iInf _).mp hP, tendsto_iInf]
      intro r
      rw [tendsto_comap_iff]
      have hr := r.property.tendsto
      change Tendsto (r.val ∘ tmul) (𝓝 0) (𝓝 (r.val (tmul 0))) at hr
      rwa [hzero, show r.val (0 : P) = 0 from map_zero r.val] at hr
    exact hq.continuousAt.comp ht)
  let U := {x : E // a x ≤ 1}
  let r (x : U) : Seminorm ℂ (F ⊗[ℂ] G) := p.comp (A.comp (TensorProduct.mk ℂ E Q x.val))
  have hr (x : U) (y : F) (z : G) : r x (y ⊗ₜ[ℂ] z) ≤ b y * s z := by
    change p ((TensorProduct.assoc ℂ E F G).symm (x.val ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z))) ≤ _
    rw [TensorProduct.assoc_symm_tmul]
    exact (hpqs _ _).trans (mul_le_mul_of_nonneg_right
      ((hqab _ _).trans (mul_le_of_le_one_left (apply_nonneg b y) x.property))
      (apply_nonneg s z))
  have hbound : BddAbove (range r) := Seminorm.bddAbove_range_iff.mpr fun t ↦ by
    induction t using TensorProduct.inductionOn with
    | tmul y z => exact ⟨b y * s z, forall_mem_range.mpr fun x ↦ hr x y z⟩
    | add t₁ t₂ h₁ h₂ =>
        obtain ⟨B₁, h₁⟩ := h₁
        obtain ⟨B₂, h₂⟩ := h₂
        exact ⟨B₁ + B₂, forall_mem_range.mpr fun x ↦ (map_add_le_add (r x) t₁ t₂).trans
          (add_le_add (h₁ (mem_range_self x)) (h₂ (mem_range_self x)))⟩
  let d : Seminorm ℂ (F ⊗[ℂ] G) := ⨆ x, r x
  have hd : ContinuousAt (fun v : F × G ↦ d (v.1 ⊗ₜ[ℂ] v.2)) 0 := by
    have : Nonempty U := ⟨⟨0, by simp⟩⟩
    rw [ContinuousAt, Prod.fst_zero, Prod.snd_zero, zero_tmul, map_zero d]
    refine squeeze_zero (g := fun v : F × G ↦ b v.1 * s v.2)
      (fun _ ↦ apply_nonneg d _) (fun v ↦ ?_) ?_
    · exact (Seminorm.iSup_apply hbound).trans_le (ciSup_le fun x ↦ hr x v.1 v.2)
    · have h : Continuous (fun v : F × G ↦ b v.1 * s v.2) :=
        (hb.comp continuous_fst).mul (hs.comp continuous_snd)
      simpa only [Prod.fst_zero, Prod.snd_zero, map_zero, zero_mul] using
        (h.continuousAt (x := (0 : F × G))).tendsto
  let hQ := withGeneratingSeminorms_spec (F ⊗[ℂ] G)
    (fun q : {q : Seminorm ℂ (F ⊗[ℂ] G) //
      ContinuousAt (fun v : F × G ↦ q (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ q.val)
  have hdcont : Continuous (fun t : Q ↦ d t) := hQ.continuous_seminorm ⟨d, hd⟩
  let c : Seminorm ℂ (E ⊗[ℂ] Q) := p.comp A
  have hc : ContinuousAt (fun v : E × Q ↦ c (v.1 ⊗ₜ[ℂ] v.2)) 0 := by
    rw [ContinuousAt, Prod.fst_zero, Prod.snd_zero, zero_tmul,
      map_zero c]
    refine squeeze_zero' (g := fun v : E × Q ↦ d v.2)
      (Eventually.of_forall fun _ ↦ apply_nonneg c _) ?_ ?_
    · have hU : a.closedBall 0 1 ∈ 𝓝 (0 : E) :=
        mem_of_superset (a.ball_mem_nhds ha one_pos) (a.ball_subset_closedBall _ _)
      have hnear := continuous_fst.continuousAt (x := (0 : E × Q)).preimage_mem_nhds hU
      filter_upwards [hnear] with v hv
      exact (le_ciSup hbound ⟨v.1, a.mem_closedBall_zero.mp hv⟩ :
        r ⟨v.1, a.mem_closedBall_zero.mp hv⟩ ≤ d) v.2
    · have h : Continuous (fun v : E × Q ↦ d v.2) := hdcont.comp continuous_snd
      have ht := (h.continuousAt (x := (0 : E × Q))).tendsto
      change Tendsto (fun v : E × Q ↦ d v.2) (𝓝 0) (𝓝 (d (0 : Q))) at ht
      rwa [show d (0 : Q) = 0 from map_zero d] at ht
  let hEQ := withGeneratingSeminorms_spec (E ⊗[ℂ] Q)
    (fun q : {q : Seminorm ℂ (E ⊗[ℂ] Q) //
      ContinuousAt (fun v : E × Q ↦ q (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ q.val)
  exact hEQ.continuous_seminorm ⟨c, hc⟩

/-- Rebracketing an outer injective tensor is continuous when the comparison
for the new inner tensor has a continuous inverse. -/
private theorem continuous_injectiveTensor_projectiveTensor_assoc {F G : Type*}
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G]
    [PolynormableSpace ℂ E]
    (hFG : @Continuous (InjectiveTensor F G) (ProjectiveTensor F G) _ _ id) :
    @Continuous (InjectiveTensor (ProjectiveTensor E F) G)
      (InjectiveTensor E (ProjectiveTensor F G)) _ _ (TensorProduct.assoc ℂ E F G) := by
  let P := ProjectiveTensor E F
  let Q := ProjectiveTensor F G
  let A : InjectiveTensor P G →ₗ[ℂ] InjectiveTensor E Q :=
    (TensorProduct.assoc ℂ E F G).toLinearMap
  change Continuous A
  refine (withGeneratingSeminorms_spec (E ⊗[ℂ] Q) _).continuous_of_continuous_comp A
    fun ⟨U, V⟩ ↦ ?_
  let p (YZ : {Y : Set F // Y ∈ 𝓝 0} × {Z : Set G // Z ∈ 𝓝 0}) :
      Seminorm ℂ (F ⊗[ℂ] G) := injectiveTensorSeminorm YZ.1 YZ.2
  have hV : (V.val : Set (InjectiveTensor F G)) ∈ 𝓝 (0 : InjectiveTensor F G) :=
    hFG.continuousAt.preimage_mem_nhds V.property
  obtain ⟨⟨J, δ⟩, hδ, hJV⟩ :=
    (withGeneratingSeminorms_spec (F ⊗[ℂ] G) p).hasBasis_zero_ball.mem_iff.mp hV
  have hcomparison : @Continuous P (InjectiveTensor E F) _ _ id :=
    (uniformContinuous_tensorComparison E F).continuous
  let W (Y : {Y : Set F // Y ∈ 𝓝 0}) : {W : Set P // W ∈ 𝓝 0} := by
    have h : Continuous (fun t : InjectiveTensor E F ↦ injectiveTensorSeminorm U Y t) :=
      (withGeneratingSeminorms_spec (E ⊗[ℂ] F) _).continuous_seminorm (U, Y)
    exact ⟨(injectiveTensorSeminorm U Y).ball 0 1, Seminorm.ball_mem_nhds
      (show Continuous (fun t : P ↦ injectiveTensorSeminorm U Y t) from h.comp hcomparison) one_pos⟩
  let c (φ : StrongDual.polar ℂ U.val) : P →ₗ[ℂ] F :=
    (TensorProduct.lid ℂ F).toLinearMap.comp (φ.val.toLinearMap.rTensor F)
  have hpair (φ : StrongDual.polar ℂ U.val) (ψ : StrongDual ℂ F) :
      ψ.toLinearMap.comp (c φ) = tensorDualForm φ.val ψ := by
    apply TensorProduct.ext'
    intro x y
    rw [tensorDualForm_tmul]
    change ψ (φ.val x • y) = _
    rw [map_smul, smul_eq_mul]
  have hbound (φ : StrongDual.polar ℂ U.val) (YZ : {Y : Set F // Y ∈ 𝓝 0} ×
      {Z : Set G // Z ∈ 𝓝 0}) (t : P ⊗[ℂ] G) :
      p YZ ((c φ).rTensor G t) ≤ injectiveTensorSeminorm (W YZ.1) YZ.2 t := by
    change injectiveTensorSeminorm YZ.1 YZ.2
      (show F ⊗[ℂ] G from (c φ).rTensor G t) ≤ _
    rw [(injectiveSeminorm_eq_ciSup YZ.1 YZ.2 ((c φ).rTensor G t)).2]
    have : Nonempty (StrongDual.polar ℂ YZ.1.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    have : Nonempty (StrongDual.polar ℂ YZ.2.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
    apply ciSup_le
    rintro ⟨ψ, χ⟩
    let l : StrongDual ℂ P := ⟨ψ.val.toLinearMap.comp (c φ),
      (ψ.val.continuous.comp (continuous_injectiveTensor_contract φ.val)).comp hcomparison⟩
    have hl : l ∈ StrongDual.polar ℂ (W YZ.1).val := by
      intro x hx
      have hsup := injectiveSeminorm_eq_ciSup U YZ.1 x
      change ‖(ψ.val.toLinearMap.comp (c φ)) x‖ ≤ 1
      rw [hpair]
      exact (le_ciSup hsup.1 (φ, ψ)).trans (hsup.2 ▸
        ((Seminorm.mem_ball_zero _).mp hx).le)
    have heq : (tensorDualForm ψ.val χ.val).comp ((c φ).rTensor G) =
        tensorDualForm l χ.val := by
      apply TensorProduct.ext'
      intro x y
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, tensorDualForm_tmul]
      rfl
    have hsup := injectiveSeminorm_eq_ciSup (W YZ.1) YZ.2 t
    rw [hsup.2, show tensorDualForm ψ.val χ.val ((c φ).rTensor G t) = tensorDualForm l χ.val t
      from DFunLike.congr_fun heq t]
    exact le_ciSup hsup.1 (⟨l, hl⟩, χ)
  let s (YZ : {Y : Set F // Y ∈ 𝓝 0} × {Z : Set G // Z ∈ 𝓝 0}) :
      Seminorm ℂ (InjectiveTensor P G) := injectiveTensorSeminorm (W YZ.1) YZ.2
  have hs : Continuous (J.sup s : Seminorm ℂ (InjectiveTensor P G)) :=
    Seminorm.continuous_finsetSup fun YZ _ ↦ by
      change Continuous (fun t : InjectiveTensor P G ↦ injectiveTensorSeminorm (W YZ.1) YZ.2 t)
      exact (withGeneratingSeminorms_spec (P ⊗[ℂ] G) _).continuous_seminorm (W YZ.1, YZ.2)
  apply Seminorm.continuous' (r := 1)
  refine mem_of_superset (Seminorm.ball_mem_nhds hs hδ) fun t ht ↦ ?_
  rw [Seminorm.mem_closedBall_zero]
  change injectiveTensorSeminorm U V (A t) ≤ 1
  rw [(injectiveSeminorm_eq_ciSup U V (A t)).2]
  have : Nonempty (StrongDual.polar ℂ U.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  have : Nonempty (StrongDual.polar ℂ V.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  apply ciSup_le
  rintro ⟨φ, l⟩
  have heq : (tensorDualForm φ.val l.val).comp A = l.val.toLinearMap.comp ((c φ).rTensor G) := by
    apply TensorProduct.ext'
    intro x z
    let L : P →ₗ[ℂ] ℂ := ((tensorDualForm φ.val l.val).comp A).comp
      ((TensorProduct.mk ℂ P G).flip z)
    let R : P →ₗ[ℂ] ℂ := (l.val.toLinearMap.comp ((c φ).rTensor G)).comp
      ((TensorProduct.mk ℂ P G).flip z)
    suffices L = R from DFunLike.congr_fun this x
    apply TensorProduct.ext'
    intro a b
    let y : Q := b ⊗ₜ[ℂ] z
    change tensorDualForm φ.val l.val (a ⊗ₜ[ℂ] y) = l.val (φ.val a • y)
    rw [tensorDualForm_tmul, map_smul, smul_eq_mul]
  rw [show tensorDualForm φ.val l.val (A t) = l.val ((c φ).rTensor G t) from
    DFunLike.congr_fun heq t]
  apply l.property
  apply hJV
  have ht' : (J.sup s) t < δ := (J.sup s).mem_ball_zero.mp ht
  change (c φ).rTensor G t ∈ (J.sup p).ball 0 δ
  apply (J.sup p).mem_ball_zero.mpr
  refine (Seminorm.finset_sup_apply_le (apply_nonneg (J.sup s) t) fun YZ hYZ ↦
    (hbound φ YZ t).trans ?_).trans_lt ht'
  exact (Finset.le_sup (f := s) hYZ : s YZ ≤ J.sup s) t

/-- The continuous comparison into the Hausdorff injective tensor topology
makes the projective tensor topology Hausdorff. -/
private theorem projectiveTensor_t2_of_comparison {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y] [T2Space Y] :
    T2Space (ProjectiveTensor X Y) :=
  T2Space.of_injective_continuous (X := ProjectiveTensor X Y) (Y := InjectiveTensor X Y)
    (f := (id : ProjectiveTensor X Y → InjectiveTensor X Y))
    Function.injective_id (uniformContinuous_tensorComparison X Y).continuous

/-- Paper: Lemma C.2.4.10(3), p. 689. The projective tensor product of two nuclear
spaces is nuclear. -/
theorem isNuclearTVS_projectiveTensor {F : Type w}
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsNuclearTVS.{max v w, u} E) (hF : IsNuclearTVS.{max v u, w} F) :
    IsNuclearTVS.{v, max u w} (ProjectiveTensor E F) := by
  let := hE.1
  let := hE.2.1
  let := hF.1
  let := hF.2.1
  refine ⟨projectiveTensor_t2_of_comparison, inferInstance, ?_⟩
  intro G _ _ _ hG sG
  let : PolynormableSpace ℂ G := hG
  let : T2Space G := sG
  let Q := ProjectiveTensor F G
  let : T2Space Q := projectiveTensor_t2_of_comparison
  have hFG : @Continuous (InjectiveTensor F G) (ProjectiveTensor F G) _ _ id :=
    (hF.2.2 G _ _ _ hG sG).isInducing.continuous_iff.mpr
      (@continuous_id (InjectiveTensor F G) _)
  have hEQ : @Continuous (InjectiveTensor E Q) (ProjectiveTensor E Q) _ _ id :=
    (hE.2.2 Q _ _ _ inferInstance inferInstance).isInducing.continuous_iff.mpr
      (@continuous_id (InjectiveTensor E Q) _)
  have hback : @Continuous (InjectiveTensor (ProjectiveTensor E F) G)
      (ProjectiveTensor (ProjectiveTensor E F) G) _ _ id := by
    have h := (continuous_projectiveTensor_assoc_symm (E := E) (F := F) (G := G)).comp
      (hEQ.comp (continuous_injectiveTensor_projectiveTensor_assoc hFG))
    exact h.congr fun t ↦ (TensorProduct.assoc ℂ E F G).symm_apply_apply t
  exact (⟨Equiv.refl ((E ⊗[ℂ] F) ⊗[ℂ] G), (uniformContinuous_tensorComparison _ _).continuous,
    hback⟩ : ProjectiveTensor (ProjectiveTensor E F) G ≃ₜ
      InjectiveTensor (ProjectiveTensor E F) G).isHomeomorph

/-- The local absolute summability criterion can be checked on finite families whose
linear combinations with coefficients in the unit disk stay in one zero-neighborhood. -/
theorem isNuclearTVS_of_signedSum_bound [PolynormableSpace ℂ E] [T2Space E]
    (h : ∀ (q : Seminorm ℂ E), Continuous q →
      ∃ U ∈ 𝓝 (0 : E), ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
        (∀ a : Fin n → ℂ, (∀ i, ‖a i‖ ≤ 1) → (∑ i, a i • x i) ∈ U) →
          ∑ i, q (x i) ≤ C) :
    IsNuclearTVS.{v, u} E := by
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  have comparisons (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U) :
      ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
        IsAbsolutelySummingLocalBanachMap E
          (show gaugeSeminorm bU cU (absorbent_nhds_zero hU) ≤
              gaugeSeminorm bV cV (absorbent_nhds_zero hV) from
            gauge_mono (absorbent_nhds_zero hV) hVU) := by
    let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
    obtain ⟨W, hW, C, hC, hbound⟩ := h q (continuous_gauge cU hU)
    obtain ⟨s, hs, hsUW⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp (inter_mem hU hW)
    let V := s.ball 0 (1 / 2)
    have hV : V ∈ 𝓝 (0 : E) := s.ball_mem_nhds hs (by norm_num)
    have bV : Balanced ℂ V := s.balanced_ball_zero _
    have cV : Convex ℝ V := s.convex_ball _ _
    have hclosed : closure V ⊆ U ∩ W := by
      have hball : IsClosed (s.closedBall 0 (1 / 2)) := by
        rw [s.closedBall_zero_eq]
        exact isClosed_le hs continuous_const
      refine (closure_minimal (s.ball_subset_closedBall _ _) hball).trans ?_
      intro x hx
      exact hsUW (s.mem_ball_zero.mpr ((s.mem_closedBall_zero.mp hx).trans_lt (by norm_num)))
    have hVU : V ⊆ U := subset_closure.trans (hclosed.trans inter_subset_left)
    let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
    let T := localBanachMap p q (gauge_mono (absorbent_nhds_zero hV) hVU)
    refine ⟨V, hV, bV, cV, hVU, C, hC, fun n x M hM hx ↦ ?_⟩
    change ∑ i, ‖T (x i)‖ ≤ C * M
    let j : WithLocalSeminorm p →L[ℂ] LocalBanach p := Completion.toComplL
    have hDense : DenseRange (fun y : Fin n → WithLocalSeminorm p ↦ fun i ↦ j (y i)) :=
      DenseRange.piMap fun _ ↦ Completion.denseRange_coe
    -- Keep the approximation errors on the right to pass the bound to the completion.
    have bound (y : Fin n → LocalBanach p) :
        ∑ i, ‖T (y i)‖ ≤ C * (M + ∑ i, ‖y i - x i‖) := by
      refine hDense.induction_on y (isClosed_le (by fun_prop) (by fun_prop)) fun zs ↦ ?_
      let z : Fin n → E := zs
      let N := M + ∑ i, ‖j (zs i) - x i‖
      have hN : 0 ≤ N := add_nonneg hM (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
      have hsum (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) :
          p (∑ i, a i • z i) ≤ N := by
        change p ((∑ i, a i • zs i : WithLocalSeminorm p) : E) ≤ N
        rw [← localBanach_norm_coe p, ← show j _ = Completion.coe' _ from rfl, map_sum]
        obtain ⟨f, hf, hfx⟩ := exists_dual_vector'' ℂ (∑ i, j (a i • zs i))
        have heq : ‖f (∑ i, j (a i • zs i))‖ = ‖∑ i, j (a i • zs i)‖ := by
          rw [hfx]
          exact Complex.norm_of_nonneg (norm_nonneg (∑ i, j (a i • zs i)))
        rw [← heq, map_sum]
        refine (norm_sum_le _ _).trans ?_
        simp only [map_smul, norm_smul]
        refine (Finset.sum_le_sum fun i _ ↦ mul_le_of_le_one_left (norm_nonneg _) (ha i)).trans ?_
        have hdiff (i : Fin n) : ‖f (j (zs i))‖ ≤ ‖f (x i)‖ + ‖j (zs i) - x i‖ := by
          calc
            _ = ‖f (x i) + f (j (zs i) - x i)‖ := by rw [← map_add, add_sub_cancel]
            _ ≤ ‖f (x i)‖ + ‖f (j (zs i) - x i)‖ := norm_add_le _ _
            _ ≤ _ := by
              gcongr
              exact (f.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hf)
        exact (Finset.sum_le_sum fun i _ ↦ hdiff i).trans
          (by rw [Finset.sum_add_distrib]; exact add_le_add (hx f hf) le_rfl)
      have hscaled : ∑ i, q (z i) ≤ C * N := by
        refine le_of_forall_pos_le_add fun ε hε ↦ ?_
        let r := N + ε / (C + 1)
        have hr : 0 < r := by dsimp [r]; positivity
        let a : ℂ := (r : ℂ)
        have ha : ‖a‖ = r := Complex.norm_of_nonneg hr.le
        have hz := hbound n (fun i ↦ a⁻¹ • z i) (fun b hb ↦ ?_)
        · simp only [map_smul_eq_mul, norm_inv, ha, ← Finset.mul_sum] at hz
          have h := (inv_mul_le_iff₀ hr).mp hz
          calc
            _ ≤ C * r := by simpa [mul_comm] using h
            _ ≤ C * N + ε := by
              dsimp [r]
              have hε' : ε / (C + 1) * (C + 1) = ε := div_mul_cancel₀ _ (by positivity)
              nlinarith [show 0 ≤ ε / (C + 1) by positivity]
        · have heq : (∑ i, b i • a⁻¹ • z i) = a⁻¹ • ∑ i, b i • z i := by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _
          apply (hclosed.trans inter_subset_right)
          apply (gauge_le_one_iff_mem_closure cV hV).mp
          change p (∑ i, b i • a⁻¹ • z i) ≤ 1
          rw [heq, map_smul_eq_mul, norm_inv, ha]
          apply (inv_mul_le_iff₀ hr).mpr
          exact (hsum b hb).trans (by dsimp [r]; linarith [show 0 ≤ ε / (C + 1) by positivity])
      have hnorm (i : Fin n) : ‖T (j (zs i))‖ = q (z i) := by
        exact (congrArg norm (localBanachMap_coe p q _ (zs i))).trans (localBanach_norm_coe q _)
      simpa only [hnorm] using hscaled
    simpa using bound x
  refine (isNuclearTVS_iff_localBanach_series E).mpr fun U hU bU cU ↦ ?_
  obtain ⟨V₁, hV₁, bV₁, cV₁, h₁, s₁⟩ := comparisons U hU bU cU
  obtain ⟨V₂, hV₂, bV₂, cV₂, h₂, s₂⟩ := comparisons V₁ hV₁ bV₁ cV₁
  obtain ⟨V₃, hV₃, bV₃, cV₃, h₃, s₃⟩ := comparisons V₂ hV₂ bV₂ cV₂
  exact ⟨V₃, hV₃, bV₃, cV₃, h₃.trans (h₂.trans h₁),
    localBanachMap_hasSeries_of_three_absolutelySumming E _ _ _ s₁ s₂ s₃⟩

/-- Paper: Lemma C.2.4.11, p. 689. If the strong dual is nuclear, a bounded set
containing all unit-disk linear combinations of a finite family controls the sum
of the family's values under any fixed continuous seminorm. The bound is uniform
over the size of the family. To obtain the estimate, pair norming functionals
for the seminorm with the evaluations at the family members in the dual of the
local Banach space for uniform convergence on the bounded set. Nuclearity bounds
the trace pairing by an injective tensor seminorm. -/
private theorem exists_sum_bound_on_bounded_sets_of_isNuclearTVS_strongDual
    [PolynormableSpace ℂ E] [T2Space E] (hN : IsNuclearTVS.{v, u} (StrongDual ℂ E))
    (q : Seminorm ℂ E) (hq : Continuous q) (B : Set E) (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
      (∀ a : Fin n → ℂ, (∀ i, ‖a i‖ ≤ 1) → (∑ i, a i • x i) ∈ B) →
        ∑ i, q (x i) ≤ C := by
  classical
  let D := StrongDual ℂ E
  let : PolynormableSpace ℂ D := hN.2.1
  let : T2Space D := hN.1
  have : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
  have : ContinuousSMul ℂ E := PolynormableSpace.continuousSMul ℂ E
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let p := mappingSeminorm (E := E) (F := ℂ) ⟨B, hB⟩ ⟨normSeminorm ℂ ℂ, continuous_norm⟩
  have hp_eval (f : D) : p f = ⨆ x : B, ‖f x.val‖ := mappingSeminorm_apply _ _ f
  have hp : Continuous p := by
    apply Seminorm.continuous' (r := 1)
    filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hB
      (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with f hf
    rw [p.mem_closedBall_zero, hp_eval]
    exact Real.iSup_le (fun x ↦ (mem_ball_zero_iff.mp (hf x.property)).le) zero_le_one
  have hbound (f : D) (x : E) (hx : x ∈ B) : ‖f x‖ ≤ p f := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp
      ((NormedSpace.isVonNBounded_iff ℂ).mp (hB.image f))
    rw [hp_eval]
    exact le_ciSup (f := fun y : B ↦ ‖f y.val‖)
      ⟨R, forall_mem_range.mpr fun y ↦ hR _ (mem_image_of_mem f y.property)⟩ ⟨x, hx⟩
  -- The continuous trace pairing tests the strong-dual factor on the bounded set B.
  let H := LocalBanach p
  let F := ULift.{v} (H →L[ℂ] ℂ)
  let : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  obtain ⟨j, hj⟩ := exists_localBanach_inclusion p hp
  let b : D →ₗ[ℂ] F →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun f g ↦ g.down (j f))
    (by intros; simp) (by intros; simp) (by intros; rfl) (by intros; rfl)
  let r : InjectiveTensor D F →ₗ[ℂ] ℂ := TensorProduct.lift b
  have hrProj : Continuous (show ProjectiveTensor D F → ℂ from r) := by
    let hP := withGeneratingSeminorms_spec (D ⊗[ℂ] F)
      (fun p : {p : Seminorm ℂ (D ⊗[ℂ] F) //
        ContinuousAt (fun z : D × F ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
    let p' := (normSeminorm ℂ ℂ).comp r
    have heval : Continuous (fun z : D × F ↦ z.2.down (j z.1)) :=
      (ContinuousLinearMap.apply ℂ (E' := H) ℂ).continuous₂.comp
        ((j.continuous.comp continuous_fst).prodMk (continuous_uliftDown.comp continuous_snd))
    have hp' : ContinuousAt (fun z : D × F ↦ p' (z.1 ⊗ₜ[ℂ] z.2)) 0 :=
      heval.norm.continuousAt
    exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp
      (show ProjectiveTensor D F →ₗ[ℂ] ℂ from r) fun _ ↦ hP.continuous_seminorm ⟨p', hp'⟩
  let eqv := (hN.2.2 F inferInstance inferInstance inferInstance inferInstance inferInstance).homeomorph
  have hback : Continuous (show InjectiveTensor D F → ProjectiveTensor D F from id) :=
    eqv.continuous_symm.congr fun z ↦ eqv.apply_symm_apply z
  let l : StrongDual ℂ (InjectiveTensor D F) := ⟨r, hrProj.comp hback⟩
  obtain ⟨U, V, hUV⟩ := exists_injectiveTensorSeminorm_bound l
  let A : Set D := {f | ∀ x, ‖f x‖ ≤ q x}
  have hA : IsVonNBounded ℂ A := by
    apply ContinuousLinearMap.isVonNBounded_iff.mpr
    intro S hS
    obtain ⟨C, _, hC⟩ := (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mp
      hS ⟨q, hq⟩
    apply (NormedSpace.isVonNBounded_iff ℂ).mpr
    refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
    rintro _ ⟨f, hf, x, hx, rfl⟩
    exact (hf x).trans (hC x hx).le
  obtain ⟨R, hR, hRU⟩ := (hA U.property).exists_pos
  have hR' (φ : StrongDual.polar ℂ U.val) (f : D) (hf : f ∈ A) : ‖φ.val f‖ ≤ R := by
    obtain ⟨g, hg, rfl⟩ := hRU (R : ℂ) (by rw [Complex.norm_of_nonneg hR.le]) hf
    rw [map_smul, norm_smul, Complex.norm_of_nonneg hR.le]
    exact mul_le_of_le_one_right hR.le (φ.property g hg)
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp V.property
  have hδ' (ψ : StrongDual.polar ℂ V.val) : ‖ψ.val‖ ≤ δ⁻¹ := by
    have hψ : ψ.val ∈ StrongDual.polar ℂ (Metric.ball (0 : F) δ) :=
      fun y hy ↦ ψ.property y (hδV hy)
    rw [NormedSpace.polar_ball hδ] at hψ
    exact mem_closedBall_zero_iff.mp hψ
  refine ⟨R * δ⁻¹, by positivity, fun n x hx ↦ ?_⟩
  have hxB (i : Fin n) : x i ∈ B := by
    simpa [Pi.single_apply, Finset.sum_ite_eq'] using hx (Pi.single i 1) fun k ↦ by
      by_cases hk : k = i <;> simp [hk]
  -- The evaluations extend to the completion. Their unit-disk combinations have norm at most one.
  let e₀ (i : Fin n) : WithLocalSeminorm p →L[ℂ] ℂ :=
    (show WithLocalSeminorm p →ₗ[ℂ] ℂ from
      ((ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (x i)) : D →L[ℂ] ℂ).toLinearMap).mkContinuous
        1 (fun f ↦ (hbound f (x i) (hxB i)).trans_eq (one_mul _).symm)
  let e (i : Fin n) : H →L[ℂ] ℂ := (e₀ i).fromCompletion
  have he (i : Fin n) (f : D) : e i (j f) = f (x i) := by
    rw [hj]
    exact (e₀ i).fromCompletion_apply_coe _
  have hesum (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) :
      ‖∑ i, a i • (ULift.up (e i) : F)‖ ≤ 1 := by
    let e' : H →L[ℂ] ℂ := ∑ i, a i • e i
    have he' : ‖e'‖ ≤ 1 := by
      apply e'.opNorm_le_bound zero_le_one
      intro y
      refine Completion.induction_on y (isClosed_le e'.continuous.norm (by fun_prop)) fun f ↦ ?_
      let f' : D := f
      have hjf : j f' = (f : H) := hj f'
      rw [← hjf, one_mul]
      simp only [e', sum_apply, smul_apply, smul_eq_mul, he]
      rw [hjf, localBanach_norm_coe]
      simpa only [map_sum, map_smul, smul_eq_mul] using hbound f' _ (hx a ha)
    let lift : (H →L[ℂ] ℂ) →ₗ[ℂ] F := (ULift.moduleEquiv : F ≃ₗ[ℂ] (H →L[ℂ] ℂ)).symm
    change ‖∑ i, lift (a i • e i)‖ ≤ 1
    rw [← map_sum]
    exact he'
  obtain ⟨j', hj'⟩ := exists_localBanach_inclusion q hq
  choose g hg hgx using fun i : Fin n ↦ exists_dual_vector'' ℂ (j' (x i))
  let f (i : Fin n) : D := (g i).comp j'
  have hf (i : Fin n) : f i ∈ A := fun y ↦ by
    have hnorm : ‖j' y‖ = q y := (congrArg norm (hj' y)).trans (localBanach_norm_coe q _)
    change ‖g i (j' y)‖ ≤ q y
    rw [← hnorm]
    exact ((g i).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hg i))
  let z : D ⊗[ℂ] F := ∑ i, f i ⊗ₜ[ℂ] (ULift.up (e i) : F)
  have hl : l z = (∑ i, q (x i) : ℝ) := by
    change (TensorProduct.lift b) (∑ i, f i ⊗ₜ[ℂ] (ULift.up (e i) : F)) = _
    rw [Complex.ofReal_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change e i (j (f i)) = _
    rw [he]
    change g i (j' (x i)) = _
    rw [hgx i, hj', localBanach_norm_coe]
    rfl
  have hnorm : ‖l z‖ = ∑ i, q (x i) := by
    rw [hl]
    exact Complex.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ apply_nonneg q _)
  rw [← hnorm]
  refine (hUV z).trans ?_
  rw [(injectiveSeminorm_eq_ciSup U V z).2]
  have : Nonempty (StrongDual.polar ℂ U.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  have : Nonempty (StrongDual.polar ℂ V.val) := (StrongDual.polar_nonempty ℂ _).to_subtype
  apply ciSup_le
  rintro ⟨φ, ψ⟩
  have hψ : (∑ i, ‖ψ.val (ULift.up (e i) : F)‖) ≤ δ⁻¹ := by
    choose a ha hphase using fun i : Fin n ↦ Complex.exists_norm_mul_eq_self (ψ.val (ULift.up (e i) : F))
    have ha' (i : Fin n) : a i ≠ 0 := norm_ne_zero_iff.mp (by rw [ha i]; exact one_ne_zero)
    have hphase' (i : Fin n) :
        (a i)⁻¹ * ψ.val (ULift.up (e i) : F) = (‖ψ.val (ULift.up (e i) : F)‖ : ℂ) := by
      calc
        _ = (a i)⁻¹ * (a i * (‖ψ.val (ULift.up (e i) : F)‖ : ℂ)) :=
          congrArg ((a i)⁻¹ * ·) (hphase i).symm
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ha' i), one_mul]
    let s : F := ∑ i, (a i)⁻¹ • (ULift.up (e i) : F)
    have hs : ‖s‖ ≤ 1 := hesum _ fun i ↦ by rw [norm_inv, ha, inv_one]
    have hψs : ψ.val s = (∑ i, ‖ψ.val (ULift.up (e i) : F)‖ : ℝ) := by
      rw [Complex.ofReal_sum]
      simp only [s, map_sum, map_smul, smul_eq_mul, hphase']
    calc
      _ = ‖ψ.val s‖ := by
        rw [hψs]
        exact (Complex.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).symm
      _ ≤ ‖ψ.val‖ * ‖s‖ := ψ.val.le_opNorm s
      _ ≤ δ⁻¹ := (mul_le_of_le_one_right (norm_nonneg _) hs).trans (hδ' ψ)
  change ‖tensorDualForm φ.val ψ.val z‖ ≤ R * δ⁻¹
  simp only [z, map_sum, tensorDualForm_tmul]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i, R * ‖ψ.val (ULift.up (e i) : F)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hR' φ _ (hf i)) (norm_nonneg _)
    _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hψ hR.le

/-- For a metrizable polynormable space, a bound for sums of seminorm values on
every bounded set of unit-disk combinations gives a bound on a zero-neighborhood. -/
private theorem exists_sum_bound_on_nhds_of_bounded [PolynormableSpace ℂ E] [TopologicalSpace.MetrizableSpace E]
    (q : Seminorm ℂ E) (h : ∀ B : Set E, IsVonNBounded ℂ B →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
        (∀ a : Fin n → ℂ, (∀ i, ‖a i‖ ≤ 1) → (∑ i, a i • x i) ∈ B) →
          ∑ i, q (x i) ≤ C) :
    ∃ U ∈ 𝓝 (0 : E), ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
      (∀ a : Fin n → ℂ, (∀ i, ‖a i‖ ≤ 1) → (∑ i, a i • x i) ∈ U) →
        ∑ i, q (x i) ≤ C := by
  classical
  by_contra! hfail
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  choose n x hx hlower using fun k : ℕ ↦ hfail (U k) (hU.mem k) (k : ℝ) (Nat.cast_nonneg k)
  -- The tail is small in any fixed seminorm. Only finitely many families precede it.
  let B : Set E := {y | ∃ k : ℕ, ∃ a : Fin (n k) → ℂ,
    (∀ i, ‖a i‖ ≤ 1) ∧ (∑ i, a i • x k i) = y}
  have hB : IsVonNBounded ℂ B := by
    apply (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mpr
    rintro ⟨p, hp⟩
    obtain ⟨j, _, hj⟩ := hU.1.mem_iff.mp (p.ball_mem_nhds hp one_pos)
    let M := ∑ k ∈ Finset.range j, ∑ i, p (x k i)
    have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ apply_nonneg p _
    refine ⟨M + 1, by linarith, ?_⟩
    rintro _ ⟨k, a, ha, rfl⟩
    change p (∑ i, a i • x k i) < M + 1
    by_cases hk : j ≤ k
    · have hmem := hj (hU.antitone hk (hx k a ha))
      exact ((p.mem_ball_zero.mp hmem).trans_le (by linarith))
    · refine lt_of_le_of_lt ?_ (lt_add_of_pos_right M one_pos)
      calc
        p (∑ i, a i • x k i) ≤ ∑ i, p (a i • x k i) :=
          Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
        _ ≤ ∑ i, p (x k i) := by
          apply Finset.sum_le_sum
          intro i _
          rw [map_smul_eq_mul]
          exact mul_le_of_le_one_left (apply_nonneg p _) (ha i)
        _ ≤ M := Finset.single_le_sum (f := fun k ↦ ∑ i, p (x k i))
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ apply_nonneg p _)
          (Finset.mem_range.mpr (lt_of_not_ge hk))
  obtain ⟨C, _, hC⟩ := h B hB
  obtain ⟨k, hk⟩ := exists_nat_gt C
  exact (not_lt_of_ge (hC (n k) (x k) fun a ha ↦ ⟨k, a, ha, rfl⟩)) (hk.trans (hlower k))

/-- A series cover of each bounded set of the primal space gives absolute
summability bounds for the seminorms of its strong dual. -/
private theorem isNuclearTVS_strongDual_of_bounded_series_cover [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E]
    (h : ∀ B : Set E, IsVonNBounded ℂ B →
      ∃ (c : ℕ → ℂ) (x : ℕ → E), Summable (fun k ↦ ‖c k‖) ∧ IsVonNBounded ℂ (range x) ∧
        ∀ y ∈ B, ∃ a : ℕ → ℂ, (∀ k, ‖a k‖ ≤ 1) ∧ HasSum (fun k ↦ (c k * a k) • x k) y) :
    IsNuclearTVS.{v, u} (StrongDual ℂ E) := by
  classical
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let D := StrongDual ℂ E
  let S : Set (Set E) := {B | IsVonNBounded ℂ B}
  let p : S × Unit → Seminorm ℂ D := fun b ↦
    mappingSeminorm (E := E) (F := ℂ)
      ⟨b.1.val, by simpa only [S, mem_ofPred_eq] using b.1.property⟩
      ⟨normSeminorm ℂ ℂ, continuous_norm⟩
  have hp : WithSeminorms p :=
    uniformConvergenceCLM_withSeminorms (E := E) S
      (fun _ hB ↦ by simpa only [S, mem_ofPred_eq] using hB)
      (by rw [show ⋃₀ S = univ from sUnion_isVonNBounded_eq_univ, Submodule.span_univ]; simp)
      (fun _ : Unit ↦ normSeminorm ℂ ℂ) (norm_withSeminorms ℂ ℂ)
  let : PolynormableSpace ℂ D := hp.toPolynormableSpace
  apply isNuclearTVS_of_signedSum_bound
  intro q hq
  obtain ⟨s, K, _, hK⟩ := Seminorm.bound_of_continuous hp q hq
  let B := ⋃ b ∈ s, (b.1.val : Set E)
  have hB : IsVonNBounded ℂ B := by
    exact (isVonNBounded_biUnion s.finite_toSet).mpr fun b _ ↦ by simpa only [S, mem_ofPred_eq] using b.1.property
  obtain ⟨c, x, hc, hx, hcover⟩ := h B hB
  let W : Set D := {f | MapsTo f (range x) (Metric.ball (0 : ℂ) 1)}
  have hW : W ∈ 𝓝 (0 : D) :=
    ContinuousLinearMap.eventually_nhds_zero_mapsTo hx (Metric.ball_mem_nhds _ one_pos)
  refine ⟨W, hW, (K : ℝ) * (∑' k, ‖c k‖), by positivity, fun n f hf ↦ ?_⟩
  have hsum (k : ℕ) : ∑ i, ‖f i (x k)‖ ≤ 1 := by
    choose a ha heq using fun i : Fin n ↦ Complex.exists_norm_mul_eq_self (f i (x k))
    have ha' (i : Fin n) : a i ≠ 0 := norm_ne_zero_iff.mp (by rw [ha i]; exact one_ne_zero)
    have hphase (i : Fin n) : (a i)⁻¹ * f i (x k) = (‖f i (x k)‖ : ℂ) := by
      calc
        _ = (a i)⁻¹ * (a i * (‖f i (x k)‖ : ℂ)) := congrArg ((a i)⁻¹ * ·) (heq i).symm
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (ha' i), one_mul]
    have hz := hf (fun i ↦ (a i)⁻¹) (fun i ↦ by rw [norm_inv, ha, inv_one]) (mem_range_self k)
    change (∑ i, (a i)⁻¹ • f i) (x k) ∈ Metric.ball 0 1 at hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have heval : (∑ i, (a i)⁻¹ • f i) (x k) = ((∑ i, ‖f i (x k)‖ : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      simp only [sum_apply, smul_apply, smul_eq_mul, hphase]
    rw [heval, Complex.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg (f i (x k)))] at hz
    exact hz.le
  have hmajorant (i : Fin n) : Summable (fun k ↦ ‖c k‖ * ‖f i (x k)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦
      mul_le_of_le_one_right (norm_nonneg _) ((Finset.single_le_sum
        (fun j _ ↦ norm_nonneg (f j (x k))) (Finset.mem_univ i)).trans (hsum k))) hc
  have heval (i : Fin n) (y : E) (hy : y ∈ B) :
      ‖f i y‖ ≤ ∑' k, ‖c k‖ * ‖f i (x k)‖ := by
    obtain ⟨a, ha, hseries⟩ := hcover y hy
    have hseries' : HasSum (fun k ↦ c k * a k * f i (x k)) (f i y) := by
      convert hseries.map (f i) (f i).continuous using 1
      funext k
      exact ((f i).map_smul (c k * a k) (x k)).symm
    have hterm (k : ℕ) : ‖c k * a k * f i (x k)‖ ≤ ‖c k‖ * ‖f i (x k)‖ := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (ha k)) (norm_nonneg _)
    have hs' := Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) hterm (hmajorant i)
    rw [← hseries'.tsum_eq]
    exact (norm_tsum_le_tsum_norm hs').trans (hs'.tsum_le_tsum hterm (hmajorant i))
  have hdom (i : Fin n) : q (f i) ≤ (K : ℝ) * ∑' k, ‖c k‖ * ‖f i (x k)‖ := by
    have hr : 0 ≤ ∑' k, ‖c k‖ * ‖f i (x k)‖ := tsum_nonneg fun _ ↦ by positivity
    have hp' : ∀ b ∈ s, p b (f i) ≤ ∑' k, ‖c k‖ * ‖f i (x k)‖ := by
      intro b hb
      change mappingSeminorm (E := E) (F := ℂ) _ _ (f i) ≤ _
      rw [mappingSeminorm_apply]
      exact Real.iSup_le (fun y ↦ heval i y.val (mem_iUnion₂.mpr ⟨b, hb, y.property⟩)) hr
    have hs' := Seminorm.finset_sup_apply_le hr hp'
    exact (hK (f i)).trans (mul_le_mul_of_nonneg_left hs' K.coe_nonneg)
  calc
    ∑ i, q (f i) ≤ ∑ i, (K : ℝ) * ∑' k, ‖c k‖ * ‖f i (x k)‖ :=
      Finset.sum_le_sum fun i _ ↦ hdom i
    _ = (K : ℝ) * ∑' k, ∑ i, ‖c k‖ * ‖f i (x k)‖ := by
      rw [← Finset.mul_sum, Summable.tsum_finsetSum fun i _ ↦ hmajorant i]
    _ ≤ _ := by
      have hle (k : ℕ) : ∑ i, ‖c k‖ * ‖f i (x k)‖ ≤ ‖c k‖ := by
        rw [← Finset.mul_sum]
        exact mul_le_of_le_one_right (norm_nonneg _) (hsum k)
      have hs' := Summable.of_nonneg_of_le (fun k ↦ Finset.sum_nonneg fun _ _ ↦ by positivity) hle hc
      exact mul_le_mul_of_nonneg_left (hs'.tsum_le_tsum hle hc) K.coe_nonneg

/-- A linear map from a final locally convex topology to a polynormable space is
continuous if its composites with the defining maps are continuous. -/
theorem continuous_of_locallyConvexFinalTopology
    {I : Type*} {X : I → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, TopologicalSpace (X i)] {D G : Type*} [AddCommGroup D] [Module ℂ D]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G]
    (j : ∀ i, X i →ₗ[ℂ] D) (g : D →ₗ[ℂ] G) (hg : ∀ i, Continuous (g ∘ j i)) :
    letI := locallyConvexFinalTopology j
    Continuous g := by
  let := locallyConvexFinalTopology j
  have hD : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D // ∀ i, Continuous (p ∘ j i)} → Seminorm ℂ D) := ⟨rfl⟩
  let := hD.isTopologicalAddGroup
  exact (PolynormableSpace.withSeminorms ℂ G).continuous_of_continuous_comp g fun p ↦
    hD.continuous_seminorm ⟨p.val.comp g, fun i ↦ p.property.comp (hg i)⟩

/-- Each coordinate projection is continuous for the final locally convex
topology on the direct sum. -/
private theorem continuous_natDirectSum_component {X : ℕ → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, PolynormableSpace ℂ (X i)] (i : ℕ) :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
    Continuous (DirectSum.component ℂ ℕ X i) := by
  apply continuous_of_locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
  intro k
  change Continuous ((DirectSum.component ℂ ℕ X i).comp (DirectSum.lof ℂ ℕ X k))
  by_cases h : k = i
  · subst k
    simpa only [DirectSum.component_comp_lof_same, LinearMap.id_coe] using
      (continuous_id : Continuous (id : X i → X i))
  · rw [DirectSum.component_comp_lof, dite_eq_right h]
    exact continuous_const

open scoped NNReal Pointwise in
/-- The tensor comparison for a countable locally convex direct sum with a normed
second factor is a homeomorphism if the comparisons on the summands are homeomorphisms.
Geometric weights combine the seminorm bounds on the summands. -/
private theorem natDirectSum_tensorComparison {X : ℕ → Type u} {F : Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    [∀ i, PolynormableSpace ℂ (X i)] [∀ i, T2Space (X i)]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (hX : ∀ i, @IsHomeomorph (ProjectiveTensor (X i) F) (InjectiveTensor (X i) F) _ _ id) :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
    T2Space (⨁ i, X i) →
    @IsHomeomorph (ProjectiveTensor (⨁ i, X i) F) (InjectiveTensor (⨁ i, X i) F) _ _ id := by
  classical
  let D := ⨁ i, X i
  let j := DirectSum.lof ℂ ℕ X
  let : TopologicalSpace D := locallyConvexFinalTopology j
  intro hT2
  let : T2Space D := hT2
  have hD : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D // ∀ i, Continuous (p ∘ j i)} → Seminorm ℂ D) := ⟨rfl⟩
  let : PolynormableSpace ℂ D := hD.toPolynormableSpace
  let : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  let pr := DirectSum.component ℂ ℕ X
  have hpr (i : ℕ) : Continuous (pr i) := continuous_natDirectSum_component i
  let prL (i : ℕ) : D →L[ℂ] X i := ⟨pr i, hpr i⟩
  have hj (i : ℕ) : Continuous (j i) := by
    let := PolynormableSpace.isTopologicalAddGroup ℂ (X i)
    exact hD.continuous_of_continuous_comp (j i) fun p ↦ p.property i
  let jL (i : ℕ) : X i →L[ℂ] D := ⟨j i, hj i⟩
  let hP := withGeneratingSeminorms_spec (D ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (D ⊗[ℂ] F) // ContinuousAt
      (fun z : D × F ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
  have hback : Continuous (show InjectiveTensor D F → ProjectiveTensor D F from id) := by
    refine hP.continuous_of_continuous_comp
      (LinearMap.id : InjectiveTensor D F →ₗ[ℂ] ProjectiveTensor D F) fun ⟨r, hr⟩ ↦ ?_
    let rStage (i : ℕ) : Seminorm ℂ (InjectiveTensor (X i) F) := r.comp ((j i).rTensor F)
    have hrStage (i : ℕ) : Continuous (rStage i) :=
      (hX i).isQuotientMap.continuous_iff.mpr
        ((hP.continuous_seminorm ⟨r, hr⟩).comp
          (projectiveTensorMap_continuous (jL i) (ContinuousLinearMap.id ℂ F)))
    choose U V C _ hbound using fun i ↦ exists_injectiveSeminorm_bound (X := X i) univ
      univ_mem (rStage i) (hrStage i)
    choose d hd hball using fun i ↦ Metric.mem_nhds_iff.mp (V i).property
    -- Shrink each first-factor neighborhood to absorb its constant and ball radius.
    let weight (i : ℕ) : ℝ := (1 / 2) ^ i
    let scale (i : ℕ) := weight i * d i / ((C i : ℝ) + 1)
    have hscale (i : ℕ) : 0 < scale i :=
      div_pos (mul_pos (by dsimp [weight]; positivity) (hd i)) (by positivity)
    have hscaled (i : ℕ) : ((scale i : ℝ) : ℂ) • (U i).val ∈ 𝓝 (0 : X i) := by
      let := PolynormableSpace.continuousSMul ℂ (X i)
      simpa only [smul_zero] using smul_mem_nhds_smul₀ (c := (scale i : ℂ))
        (by exact_mod_cast (hscale i).ne') (U i).property
    choose q hq hqsub using fun i ↦
      (PolynormableSpace.hasBasis_zero_ball ℂ (X i)).mem_iff.mp (hscaled i)
    let Q := directSumSeminorm q
    have hQ : Continuous Q := hD.continuous_seminorm ⟨Q, fun i ↦ by
      exact (hq i).congr fun x ↦ (directSumSeminorm_lof q i x).symm⟩
    let A : {A : Set D // A ∈ 𝓝 0} := ⟨Q.ball 0 1, Q.ball_mem_nhds hQ one_pos⟩
    let B : {B : Set F // B ∈ 𝓝 0} := ⟨Metric.closedBall 0 1,
      Metric.closedBall_mem_nhds _ one_pos⟩
    have hproj (i : ℕ) (x : D) (hx : x ∈ A.val) :
        pr i x ∈ ((scale i : ℝ) : ℂ) • (U i).val := by
      apply hqsub i
      rw [Seminorm.mem_ball_zero]
      refine lt_of_le_of_lt ?_ ((Q.mem_ball_zero).mp hx)
      change q i (x i) ≤ directSumSeminorm q x
      simpa only [Finset.sum_singleton] using sum_le_directSumSeminorm q x {i}
    have hstage (i : ℕ) (z : D ⊗[ℂ] F) :
        rStage i ((pr i).rTensor F z) ≤ weight i * injectiveTensorSeminorm A B z := by
      refine (hbound i _).trans ?_
      have hε : injectiveTensorSeminorm (U i) (V i) ((pr i).rTensor F z) ≤
          (scale i * (d i)⁻¹) * injectiveTensorSeminorm A B z := by
        rw [(injectiveSeminorm_eq_ciSup (U i) (V i) _).2]
        have : Nonempty (StrongDual.polar ℂ (U i).val) :=
          (StrongDual.polar_nonempty ℂ _).to_subtype
        have : Nonempty (StrongDual.polar ℂ (V i).val) :=
          (StrongDual.polar_nonempty ℂ _).to_subtype
        apply ciSup_le
        rintro ⟨φ, ψ⟩
        have heq : (tensorDualForm φ.val ψ.val).comp ((pr i).rTensor F) =
            tensorDualForm (φ.val.comp (prL i)) ψ.val := by
          apply TensorProduct.ext'
          intro x y
          simp [tensorDualForm_tmul, prL]
        rw [show tensorDualForm φ.val ψ.val ((pr i).rTensor F z) =
          tensorDualForm (φ.val.comp (prL i)) ψ.val z from DFunLike.congr_fun heq z]
        refine norm_tensorDualForm_le_mul_injectiveSeminorm A B _ _ _
          (hscale i) (inv_pos.mpr (hd i)) ?_ ?_
        · intro x hx
          obtain ⟨y, hy, hxy⟩ := hproj i x hx
          change ‖φ.val (pr i x)‖ ≤ scale i
          rw [← hxy, map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hscale i).le]
          exact mul_le_of_le_one_right (hscale i).le
            ((StrongDual.mem_polar_iff ℂ _).mp φ.property _ hy)
        · have hψ : ψ.val ∈ StrongDual.polar ℂ (Metric.ball 0 (d i)) :=
            (topDualPairing ℂ F).flip.polar_antitone (hball i) ψ.property
          rw [NormedSpace.polar_ball (hd i), Metric.mem_closedBall, dist_zero_right] at hψ
          intro y hy
          have hy' : ‖y‖ ≤ 1 := by
            simpa only [B, Metric.mem_closedBall, dist_zero_right] using hy
          exact (ψ.val.le_opNorm y).trans
            ((mul_le_of_le_one_right (norm_nonneg _) hy').trans hψ)
      calc
        _ ≤ (C i : ℝ) * ((scale i * (d i)⁻¹) * injectiveTensorSeminorm A B z) :=
          mul_le_mul_of_nonneg_left hε (C i).coe_nonneg
        _ ≤ weight i * injectiveTensorSeminorm A B z := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (apply_nonneg _ _)
          have heq : (C i : ℝ) * (scale i * (d i)⁻¹) =
              ((C i : ℝ) / ((C i : ℝ) + 1)) * weight i := by
            have hC : 0 < (C i : ℝ) + 1 := by positivity
            dsimp [scale]
            field_simp [(hd i).ne', hC.ne']
          rw [heq]
          exact mul_le_of_le_one_left (by dsimp [weight]; positivity)
            ((div_le_one (by positivity)).mpr (by linarith))
    let e := TensorProduct.directSumLeft ℂ ℂ X F
    have he (i : ℕ) :
        (DirectSum.component ℂ ℕ (fun i ↦ X i ⊗[ℂ] F) i).comp e.toLinearMap =
          (pr i).rTensor F := by
      apply TensorProduct.ext'
      intro x y
      change e (x ⊗ₜ[ℂ] y) i = (pr i).rTensor F (x ⊗ₜ[ℂ] y)
      rw [LinearMap.rTensor_tmul]
      exact TensorProduct.directSumLeft_tmul ℂ ℂ x y i
    have hrbound (z : D ⊗[ℂ] F) : r z ≤ 2 * injectiveTensorSeminorm A B z := by
      let s := (e z).support
      have hs (i : ℕ) : e.symm (DirectSum.of (fun i ↦ X i ⊗[ℂ] F) i (e z i)) =
          (j i).rTensor F ((pr i).rTensor F z) :=
        (TensorProduct.directSumLeft_symm_of ℂ ℂ (e z i)).trans
          (congrArg ((j i).rTensor F) (DFunLike.congr_fun (he i) z))
      have hsum : (∑ i ∈ s, (j i).rTensor F ((pr i).rTensor F z)) = z := by
        simpa only [map_sum, LinearEquiv.symm_apply_apply, hs] using
          congrArg e.symm (DirectSum.sum_support_of (e z))
      calc
        r z = r (∑ i ∈ s, (j i).rTensor F ((pr i).rTensor F z)) := congrArg r hsum.symm
        _ ≤ ∑ i ∈ s, rStage i ((pr i).rTensor F z) :=
          Finset.le_sum_of_subadditive r (map_zero r).le (map_add_le_add r) _ _
        _ ≤ ∑ i ∈ s, weight i * injectiveTensorSeminorm A B z :=
          Finset.sum_le_sum fun i _ ↦ hstage i z
        _ ≤ 2 * injectiveTensorSeminorm A B z := by
          rw [← Finset.sum_mul]
          refine mul_le_mul_of_nonneg_right ?_ (apply_nonneg _ _)
          exact tsum_geometric_two ▸ summable_geometric_two.sum_le_tsum s
            (fun i _ ↦ by dsimp [weight]; positivity)
    let hI := withGeneratingSeminorms_spec (D ⊗[ℂ] F)
      (fun UV : {U : Set D // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
        injectiveTensorSeminorm UV.1 UV.2)
    change @Continuous (InjectiveTensor D F) ℝ _ _ r
    exact Seminorm.continuous_of_le (q := (2 : ℝ≥0) • injectiveTensorSeminorm A B)
      ((hI.continuous_seminorm (A, B)).const_smul (2 : ℝ≥0)) hrbound
  exact (⟨Equiv.refl (D ⊗[ℂ] F), (uniformContinuous_tensorComparison D F).continuous, hback⟩ :
    ProjectiveTensor D F ≃ₜ InjectiveTensor D F).isHomeomorph

-- The final topology makes the canonical stage maps continuous by construction.
set_option linter.unusedVariables false in
/-- Paper: Lemma C.2.4.12(1), p. 689. A Hausdorff locally convex inductive limit
of a sequence of nuclear spaces is nuclear. The transition maps may have kernels. -/
theorem isNuclearTVS_directLimit {X : ℕ → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    (f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j) [DirectedSystem X (f · · ·)]
    (hf : ∀ i j h, Continuous (f i j h)) (hX : ∀ i, IsNuclearTVS.{v} (X i))
    (h : @T2Space _ (lcDirectLimitTopology f)) :
    letI := lcDirectLimitTopology f
    IsNuclearTVS.{v} (Module.DirectLimit X f) := by
  let D := ⨁ i, X i
  let L := Module.DirectLimit X f
  let j := DirectSum.lof ℂ ℕ X
  let stage := Module.DirectLimit.of ℂ ℕ X f
  let : TopologicalSpace D := locallyConvexFinalTopology j
  let : TopologicalSpace L := lcDirectLimitTopology f
  let : T2Space L := h
  let : ∀ i, PolynormableSpace ℂ (X i) := fun i ↦ (hX i).2.1
  let : ∀ i, T2Space (X i) := fun i ↦ (hX i).1
  have hD : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D // ∀ i, Continuous (p ∘ j i)} → Seminorm ℂ D) := ⟨rfl⟩
  have hL : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ L // ∀ i, Continuous (p ∘ stage i)} → Seminorm ℂ L) := ⟨rfl⟩
  let : IsTopologicalAddGroup D := hD.isTopologicalAddGroup
  let : PolynormableSpace ℂ D := hD.toPolynormableSpace
  let : PolynormableSpace ℂ L := hL.toPolynormableSpace
  let : T2Space D := by
    refine ⟨fun x y hxy ↦ ?_⟩
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra! he
      exact hxy (DFinsupp.ext he)
    exact separated_by_continuous (continuous_natDirectSum_component i) hi
  have hN : IsNuclearTVS.{v} D := by
    apply (isNuclearTVS_iff_completedTensor_banach D).mpr
    intro F _ _ _
    let : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
    exact (isHomeomorph_completedTensorComparison_iff D F).mpr
      (natDirectSum_tensorComparison (fun i ↦
        (hX i).2.2 F inferInstance inferInstance inferInstance inferInstance inferInstance)
        inferInstance)
  -- Present the limit as the quotient of the direct sum by the kernel of the canonical map.
  let q : D →ₗ[ℂ] L := DirectSum.toModule ℂ ℕ L stage
  have hqj (i : ℕ) (x : X i) : q (j i x) = stage i x := DirectSum.toModule_lof ℂ i x
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    exact ⟨j i x, hqj i x⟩
  let K := q.ker
  let Q := D ⧸ K
  let : PolynormableSpace ℂ Q := polynormableSpace_quotient K
  let e := q.quotKerEquivOfSurjective hq
  have hj (i : ℕ) : Continuous (j i) := by
    let := PolynormableSpace.isTopologicalAddGroup ℂ (X i)
    exact hD.continuous_of_continuous_comp (j i) fun p ↦ p.property i
  have hstage (i : ℕ) : Continuous (stage i) := by
    let := PolynormableSpace.isTopologicalAddGroup ℂ (X i)
    exact hL.continuous_of_continuous_comp (stage i) fun p ↦ p.property i
  have he : Continuous e := by
    apply K.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr
    change Continuous q
    exact continuous_of_locallyConvexFinalTopology j q fun i ↦
      (hstage i).congr fun x ↦ (hqj i x).symm
  have hes : Continuous e.symm := by
    apply continuous_of_locallyConvexFinalTopology stage e.symm.toLinearMap
    intro i
    refine (K.mkQL.continuous.comp (hj i)).congr fun x ↦ ?_
    change K.mkQ (j i x) = e.symm (stage i x)
    rw [← hqj]
    exact (q.quotKerEquivOfSurjective_symm_apply hq (j i x)).symm
  let eL : Q ≃L[ℂ] L := ⟨e, he, hes⟩
  let : T2Space Q := eL.symm.toHomeomorph.t2Space
  have hQ : IsNuclearTVS.{v} Q := isNuclearTVS_quotient hN K
  refine ⟨h, inferInstance, ?_⟩
  intro F _ _ _ _ _
  have hbackQ : Continuous (show InjectiveTensor Q F → ProjectiveTensor Q F from id) := by
    let eQ := (hQ.2.2 F inferInstance inferInstance inferInstance inferInstance inferInstance).homeomorph
    exact eQ.continuous_symm.congr fun z ↦ eQ.apply_symm_apply z
  let forward := eL.toContinuousLinearMap
  let backward := eL.symm.toContinuousLinearMap
  let idF := ContinuousLinearMap.id ℂ F
  have hback : Continuous (show InjectiveTensor L F → ProjectiveTensor L F from id) := by
    refine ((projectiveTensorMap_continuous forward idF).comp hbackQ |>.comp
      (injectiveTensorMap_continuous backward idF)).congr fun z ↦ ?_
    change L ⊗[ℂ] F at z
    change forward.toLinearMap.rTensor F (backward.toLinearMap.rTensor F z) = z
    rw [← LinearMap.rTensor_comp_apply, show forward.toLinearMap.comp backward.toLinearMap =
      LinearMap.id from LinearMap.ext e.apply_symm_apply, LinearMap.rTensor_id_apply]
  exact (⟨Equiv.refl (L ⊗[ℂ] F), (uniformContinuous_tensorComparison L F).continuous, hback⟩ :
    ProjectiveTensor L F ≃ₜ InjectiveTensor L F).isHomeomorph

-- Nuclearity holds for every submodule of the product, independently of the transition maps.
set_option linter.unusedVariables false in
/-- Paper: Lemma C.2.4.12(2), p. 689. The projective limit of nuclear spaces
is nuclear, with the topology on compatible families induced from the product. -/
theorem isNuclearTVS_projectiveLimit {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {X : I → Type u} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, TopologicalSpace (X i)] (f : ∀ i j, i ≤ j → X j →ₗ[ℂ] X i)
    [DirectedSystem (ι := Iᵒᵈ) X (fun {i j} h ↦ f j i h)]
    (hf : ∀ i j h, Continuous (f i j h)) (hX : ∀ i, IsNuclearTVS.{max v w, u} (X i)) :
    let L : Submodule ℂ (∀ i, X i) := ⨅ i, ⨅ j, ⨅ h : i ≤ j,
      LinearMap.ker (LinearMap.proj i - (f i j h).comp (LinearMap.proj j))
    IsNuclearTVS.{v, max u w} L := by
  intro L
  exact isNuclearTVS_submodule (isNuclearTVS_pi hX) L

/-- Paper: Remark C.2.4.13, p. 689. Hausdorffness can fail in locally convex
inductive limits, even for a sequence with nuclear stages.
Deviation: The stages are the countable product of complex lines. -/
theorem exists_directLimit_not_t2 :
    let X := fun _ : ℕ ↦ ℕ → ℂ
    ∃ f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j,
      DirectedSystem X (f · · ·) ∧ (∀ i j h, Continuous (f i j h)) ∧
        ¬ @T2Space _ (lcDirectLimitTopology f) := by
  intro X
  -- Each transition drops one coordinate for every step between the stages.
  let f : ∀ i j, i ≤ j → X i →ₗ[ℂ] X j :=
    fun i j _ ↦ LinearMap.pi fun k ↦ LinearMap.proj (k + (j - i))
  let : DirectedSystem X (f · · ·) :=
    { map_self := fun {i} x ↦ by
        funext k
        change x (k + (i - i)) = x k
        simp
      map_map := fun {k j i} hij hjk x ↦ by
        funext n
        change x (n + (k - j) + (j - i)) = x (n + (k - i))
        congr 1
        omega }
  refine ⟨f, inferInstance, fun i j h ↦ continuous_pi fun k ↦
    continuous_apply (k + (j - i)), ?_⟩
  let L := Module.DirectLimit X f
  let stage := Module.DirectLimit.of ℂ ℕ X f
  let : TopologicalSpace L := lcDirectLimitTopology f
  intro hT2
  let : T2Space L := hT2
  let P : SeminormFamily ℂ L {p : Seminorm ℂ L // ∀ i, Continuous (p ∘ stage i)} :=
    Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  have hstage : Continuous (stage 0) :=
    hP.continuous_of_continuous_comp (stage 0) fun p ↦ p.property 0
  -- The finite truncations converge to the constant sequence of ones in stage zero.
  let u (n : ℕ) : X 0 := fun k ↦ if k < n then 1 else 0
  let x : X 0 := fun _ ↦ 1
  have hu : Tendsto u atTop (𝓝 x) := by
    apply tendsto_pi_nhds.mpr
    intro k
    apply tendsto_atTop_of_eventually_const (i₀ := k + 1)
    intro n hn
    exact ite_eq_left (Nat.lt_of_succ_le hn)
  -- Their images are already zero, since the transition to stage n drops their support.
  have hzero (n : ℕ) : stage 0 (u n) = 0 := by
    have hdrop : f 0 n (Nat.zero_le n) (u n) = 0 := by
      funext k
      change (if k + (n - 0) < n then (1 : ℂ) else 0) = 0
      exact ite_eq_right (by omega)
    rw [← Module.DirectLimit.of_f (hij := Nat.zero_le n), hdrop, map_zero]
  have ht : Tendsto (fun n ↦ stage 0 (u n)) atTop (𝓝 (0 : L)) := by
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : L)) atTop (𝓝 0))
  have heq : stage 0 x = 0 := tendsto_nhds_unique (hstage.continuousAt.tendsto.comp hu) ht
  -- The constant sequence survives every transition.
  obtain ⟨n, hn, hx⟩ := Module.DirectLimit.of.zero_exact heq
  have hone : (1 : ℂ) = 0 := congrFun hx 0
  exact one_ne_zero hone

-- Remark C.2.4.14 (p. 689) gives references and explains their Hausdorff convention.

end Permanence

section Approximation

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]
  [IsTopologicalAddGroup F]

/-- Paper: (C.2.4.6)–(C.2.4.7), p. 689. The canonical map from the algebraic tensor
of the continuous dual with the target sends a pure tensor to a rank-one operator. -/
def tensorToFiniteRank : StrongDual ℂ E ⊗[ℂ] F →ₗ[ℂ] E →L[ℂ] F :=
  TensorProduct.lift
    { toFun := fun φ ↦ ContinuousLinearMap.smulRightₗ φ
      map_add' := fun φ ψ ↦ LinearMap.ext fun y ↦ ContinuousLinearMap.ext fun x ↦
        add_smul (φ x) (ψ x) y
      map_smul' := fun c φ ↦ LinearMap.ext fun y ↦ ContinuousLinearMap.ext fun x ↦
        mul_smul c (φ x) y }

/-- Paper: (C.2.4.7), p. 689. On a pure tensor the canonical map evaluates the
dual factor on the input and scales the target factor by the result. -/
theorem tensorToFiniteRank_tmul (φ : StrongDual ℂ E) (y : F) (x : E) :
    tensorToFiniteRank (φ ⊗ₜ[ℂ] y) x = φ x • y := rfl

/-- Paper: (C.2.4.6), p. 689. The canonical map from the dual tensor is injective. -/
theorem tensorToFiniteRank_injective :
    Function.Injective (tensorToFiniteRank (E := E) (F := F)) := by
  let b := Module.Free.chooseBasis ℂ F
  -- Coordinates of the dual factor along a basis of the target.
  let e : StrongDual ℂ E ⊗[ℂ] F ≃ₗ[ℂ] (Module.Free.ChooseBasisIndex ℂ F →₀ StrongDual ℂ E) :=
    (TensorProduct.congr (LinearEquiv.refl ℂ (StrongDual ℂ E)) b.repr).trans
      (TensorProduct.finsuppScalarRight ℂ ℂ (StrongDual ℂ E) _)
  have key (z : StrongDual ℂ E ⊗[ℂ] F) (i) (x : E) :
      e z i x = b.repr (tensorToFiniteRank z x) i := by
    induction z using TensorProduct.inductionOn with
    | tmul φ y =>
      simp [e, TensorProduct.finsuppScalarRight_apply_tmul_apply, tensorToFiniteRank_tmul,
        mul_comm]
    | add z w hz hw =>
      simp only [map_add, Finsupp.add_apply, ContinuousLinearMap.add_apply] at hz hw ⊢
      rw [hz, hw]
  intro z w h
  apply e.injective
  ext i x
  rw [key, key, h]

end Approximation

section ApproximationProperty

variable (E : Type u) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [T2Space E]

/-- Paper: Lemma C.2.4.15(2), p. 689. A space has the approximation property if its
finite-rank endomorphisms are dense for uniform convergence on precompact sets. -/
def HasApproximationProperty : Prop :=
  DenseRange (X := PrecompactConvergenceCLM E E) (fun z ↦ tensorToFiniteRank z)

omit [T2Space E] in
/-- Paper: Lemma C.2.4.15(2), p. 689. Unfolding the approximation property gives density
for the uniform convergence topology indexed by sets with compact closure in the completion. -/
theorem hasApproximationProperty_iff_denseRange :
    HasApproximationProperty E ↔
      DenseRange (X := E →Lᵤ[ℂ, {s | IsPrecompactInCompletion s}] E)
        (fun z ↦ tensorToFiniteRank z) := Iff.rfl

/-- Paper: Lemma C.2.4.15(2), p. 689. Density for uniform convergence on bounded sets
implies the approximation property. For a normed space the hypothesis is operator-norm density.
Deviation: This compares the two topologies on the same finite-rank maps. -/
theorem hasApproximationProperty_of_denseRange_bounded
    (h : DenseRange (X := E →L[ℂ] E) (fun z ↦ tensorToFiniteRank z)) :
    HasApproximationProperty E := by
  let S := {s : Set E | IsPrecompactInCompletion s}
  let j := ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) E S
  have hj : Continuous j :=
    ContinuousLinearMap.toUniformConvergenceCLM_continuous (RingHom.id ℂ) E S fun s hs ↦
      ((isPrecompactInCompletion_iff_totallyBounded s).mp hs).isVonNBounded ℂ
  exact j.surjective.denseRange.comp h hj

omit [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E] in
/-- Postcomposition preserves the closure of the finite-rank maps for uniform convergence
on any fixed family of sets. -/
private theorem postcomp_mem_closure_finiteRank_uniform {F G : Type*}
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [PolynormableSpace ℂ F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [PolynormableSpace ℂ G] (S : Set (Set E)) (A : F →L[ℂ] G) {T : E →L[ℂ] F}
    (hT : T ∈ closure (X := E →Lᵤ[ℂ, S] F) (range (fun z ↦ tensorToFiniteRank z))) :
    A.comp T ∈ closure (X := E →Lᵤ[ℂ, S] G) (range (fun z ↦ tensorToFiniteRank z)) := by
  let post : (E →Lᵤ[ℂ, S] F) →L[ℂ] (E →Lᵤ[ℂ, S] G) :=
    A.postcompUniformConvergenceCLM S
  change post T ∈ _
  refine Set.MapsTo.closure (f := post) ?_ post.continuous hT
  rintro _ ⟨z, rfl⟩
  let map := TensorProduct.map (LinearMap.id : StrongDual ℂ E →ₗ[ℂ] StrongDual ℂ E)
    A.toLinearMap
  refine ⟨map z, ContinuousLinearMap.ext fun x ↦ ?_⟩
  change tensorToFiniteRank (map z) x = A (tensorToFiniteRank z x)
  induction z using TensorProduct.inductionOn with
  | tmul φ y =>
    simp only [map, TensorProduct.map_tmul, LinearMap.id_apply, tensorToFiniteRank_tmul, map_smul,
      ContinuousLinearMap.coe_coe]
  | add z w hz hw => simp only [map_add, add_apply, hz, hw]

omit [T2Space E] in
/-- Postcomposition by each endomorphism takes a finite-rank approximation of the identity
to one of that endomorphism, for uniform convergence on any fixed family of sets. -/
private theorem id_mem_closure_finiteRank_iff_dense_uniform (S : Set (Set E)) :
    ContinuousLinearMap.id ℂ E ∈
      closure (X := E →Lᵤ[ℂ, S] E) (range (fun z ↦ tensorToFiniteRank z)) ↔
    DenseRange (X := E →Lᵤ[ℂ, S] E) (fun z ↦ tensorToFiniteRank z) := by
  refine ⟨fun h A ↦ ?_, fun h ↦ h _⟩
  change E →L[ℂ] E at A
  have hA := postcomp_mem_closure_finiteRank_uniform E S A h
  rwa [ContinuousLinearMap.comp_id] at hA

/-- Paper: Lemma C.2.4.15(1)–(2), p. 689. The identity is approximable by finite-rank
maps uniformly on precompact sets exactly when those maps are dense among endomorphisms. -/
theorem id_mem_closure_finiteRank_iff_dense :
    ContinuousLinearMap.id ℂ E ∈
      closure (X := PrecompactConvergenceCLM E E) (range (fun z ↦ tensorToFiniteRank z)) ↔
    HasApproximationProperty E :=
  id_mem_closure_finiteRank_iff_dense_uniform E {s | IsPrecompactInCompletion s}

/-- Paper: Lemma C.2.4.15(2)–(3), p. 689. Density of finite-rank maps for the
precompact convergence topology on endomorphisms is equivalent to the corresponding
density for all targets. -/
theorem dense_finiteRank_iff_forall_targets :
    HasApproximationProperty E ↔
      ∀ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module ℂ F) (_ : TopologicalSpace F)
        (_ : IsTopologicalAddGroup F) (_ : PolynormableSpace ℂ F) (_ : T2Space F),
        DenseRange (X := PrecompactConvergenceCLM E F) (fun z ↦ tensorToFiniteRank z) := by
  let S := {s : Set E | IsPrecompactInCompletion s}
  constructor
  · intro h F _ _ _ _ _ _ A
    change E →L[ℂ] F at A
    have hA := postcomp_mem_closure_finiteRank_uniform E S A (h (ContinuousLinearMap.id ℂ E))
    rwa [ContinuousLinearMap.comp_id] at hA
  · intro h
    let G := ULift.{v, u} E
    let e : G ≃L[ℂ] E := ContinuousLinearEquiv.ulift
    have : PolynormableSpace ℂ G :=
      e.toHomeomorph.isInducing.polynormableSpace (f := e.toLinearEquiv.toLinearMap)
    have : IsTopologicalAddGroup G := PolynormableSpace.isTopologicalAddGroup ℂ G
    have hup := h G inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance (e.symm : E →L[ℂ] G)
    apply (id_mem_closure_finiteRank_iff_dense E).mp
    simpa only [ContinuousLinearEquiv.coe_comp_coe_symm] using
      postcomp_mem_closure_finiteRank_uniform E S (e : G →L[ℂ] E) hup

/-- Applying the pulled-back tensor of finite-rank maps precomposes the operator: for a
differential `b` of the source, `λ(Σ φᵢ ⊗ yᵢ) ∘ b = λ(Σ (φᵢ ∘ b) ⊗ yᵢ)`. -/
private theorem tensorToFiniteRank_precomp_apply {S T U : Type*} [AddCommGroup S] [Module ℂ S]
    [TopologicalSpace S]
    [AddCommGroup T] [Module ℂ T] [TopologicalSpace T] [PolynormableSpace ℂ T]
    [IsTopologicalAddGroup T] [AddCommGroup U] [Module ℂ U]
    [TopologicalSpace U] (b : U →L[ℂ] S) (z : StrongDual ℂ S ⊗[ℂ] T) (x : U) :
    tensorToFiniteRank (E := U) (F := T)
        (TensorProduct.map
          { toFun := fun ψ : StrongDual ℂ S => ψ.comp b
            map_add' := fun ψ χ => by ext y; simp
            map_smul' := fun c ψ => by ext y; simp }
          (LinearMap.id : T →ₗ[ℂ] T) z) x
      = tensorToFiniteRank (E := S) (F := T) z (b x) := by
  induction z using TensorProduct.inductionOn with
  | tmul φ y =>
      rw [TensorProduct.map_tmul, tensorToFiniteRank_tmul, tensorToFiniteRank_tmul]
      rfl
  | add z w hz hw =>
      simp only [map_add, add_apply, hz, hw]

omit [T2Space E] in
/-- Precompact-convergence closure tests uniform approximation on each totally bounded set. -/
private theorem mem_closure_finiteRank_iff {F : Type*} [AddCommGroup F] [Module ℂ F] [UniformSpace F]
    [T2Space F] (T : F →L[ℂ] E) :
    T ∈ closure (X := PrecompactConvergenceCLM F E) (range (fun z ↦ tensorToFiniteRank z)) ↔
      ∀ B : Set F, TotallyBounded B → ∀ V ∈ 𝓝 (0 : E),
        ∃ z : StrongDual ℂ F ⊗[ℂ] E,
          ∀ x ∈ B, tensorToFiniteRank z x - T x ∈ V := by
  let S := {s : Set F | IsPrecompactInCompletion s}
  have hpre (s : Set F) : s ∈ S ↔ TotallyBounded s := isPrecompactInCompletion_iff_totallyBounded s
  have hne : S.Nonempty := ⟨∅, (hpre ∅).2 totallyBounded_empty⟩
  have hd : DirectedOn (· ⊆ ·) S := directedOn_of_sup_mem fun s t hs ht ↦
    (hpre _).2 (((hpre s).1 hs).union ((hpre t).1 ht))
  have hb := UniformConvergenceCLM.hasBasis_nhds_zero (RingHom.id ℂ) E S hne hd
  have hT := hb.nhds_of_zero (T : PrecompactConvergenceCLM F E)
  constructor
  · intro h B hB V hV
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := (mem_closure_iff_nhds_basis hT).mp h (B, V) ⟨(hpre B).2 hB, hV⟩
    exact ⟨z, hz⟩
  · intro h
    apply (mem_closure_iff_nhds_basis hT).mpr
    rintro ⟨B, V⟩ ⟨hB, hV⟩
    obtain ⟨z, hz⟩ := h B ((hpre B).1 hB) V hV
    exact ⟨tensorToFiniteRank z, ⟨z, rfl⟩, hz⟩

/-- Paper: Lemma C.2.4.15(2), (4), pp. 689–690. Density of finite-rank maps for
the precompact convergence topology on endomorphisms is equivalent to the corresponding
density for all sources. -/
theorem dense_finiteRank_iff_forall_sources :
    HasApproximationProperty E ↔
      ∀ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module ℂ F) (_ : UniformSpace F)
        (_ : IsUniformAddGroup F) (_ : PolynormableSpace ℂ F) (_ : T2Space F),
        DenseRange (X := PrecompactConvergenceCLM F E) (fun z ↦ tensorToFiniteRank z) := by
  constructor
  · -- (2) ⟹ (4): precompose the finite-rank approximants with the source operator.
    intro hdense F _ _ _ _ _ _ T
    change F →L[ℂ] E at T
    refine (mem_closure_finiteRank_iff E T).mpr fun B hB V hV ↦ ?_
    obtain ⟨z, hz⟩ :=
      (mem_closure_finiteRank_iff E (ContinuousLinearMap.id ℂ E)).mp
        (hdense (ContinuousLinearMap.id ℂ E)) (T '' B)
        (hB.image (T : F →L[ℂ] E).uniformContinuous) V hV
    exact ⟨TensorProduct.map
      { toFun := fun ψ : StrongDual ℂ E => ψ.comp (T : F →L[ℂ] E)
        map_add' := fun ψ χ => by ext y; rfl
        map_smul' := fun c ψ => by ext y; rfl }
      (LinearMap.id : E →ₗ[ℂ] E) z, fun x hx ↦ by
      rw [tensorToFiniteRank_precomp_apply (T : F →L[ℂ] E) z x]
      exact hz (T x) (mem_image_of_mem (T : F →L[ℂ] E) hx)⟩
  · -- (4) ⟹ (2): apply the hypothesis to the universe-raised copy of `E`.
    intro hforall
    refine (id_mem_closure_finiteRank_iff_dense E).mp ?_
    refine (mem_closure_finiteRank_iff E (ContinuousLinearMap.id ℂ E)).mpr fun B hB V hV ↦ ?_
    classical
    let G := ULift.{max u v, u} E
    letI hGadd : AddCommGroup G := ULift.addCommGroup
    letI hGmod : Module ℂ G := ULift.module'
    letI hGunif : UniformSpace G := UniformSpace.comap (fun g : G ↦ ULift.down g) ‹UniformSpace E›
    have hdownui : IsUniformInducing (fun g : G ↦ ULift.down g) :=
      (isUniformEmbedding_comap (f := fun g : G ↦ ULift.down g)
        (fun a b (h : ULift.down a = ULift.down b) => by
          cases a with
          | up a' =>
          cases b with
          | up b' =>
          exact congrArg ULift.up h)).isUniformInducing
    have hdowncont : Continuous (fun g : G ↦ ULift.down g) :=
      hdownui.uniformContinuous.continuous
    have hupcont : Continuous (fun x : E ↦ (⟨x⟩ : G)) :=
      (uniformContinuous_comap' (f := fun g : G ↦ ULift.down g)
        (g := fun x : E ↦ (⟨x⟩ : G))
        (by rw [show ((fun g : G ↦ ULift.down g) ∘ fun x : E ↦ (⟨x⟩ : G)) = id from rfl]
            exact uniformContinuous_id)).continuous
    have hdownind : IsInducing (fun g : G ↦ ULift.down g) := hdownui.isInducing
    letI hGuadd : IsUniformAddGroup G :=
      IsUniformAddGroup.comap
        (f := (⟨⟨fun g : G ↦ ULift.down g, rfl⟩, fun _ _ ↦ rfl⟩ : G →+ E))
    have hGT2 : T2Space G := by
      have hemb : IsEmbedding (fun g : G ↦ ULift.down g) :=
        ⟨hdownind, fun a b (h : ULift.down a = ULift.down b) => by
          cases a with
          | up a' =>
          cases b with
          | up b' =>
          exact congrArg ULift.up h⟩
      exact hemb.t2Space
    have hGpolyn : PolynormableSpace ℂ G :=
      hdownind.polynormableSpace (f := (ULift.moduleEquiv (R := ℂ) (M := E)).toLinearMap)
    let downCLM : G →L[ℂ] E :=
      ⟨(ULift.moduleEquiv (R := ℂ) (M := E)).toLinearMap, hdowncont⟩
    let hupCLM : E →L[ℂ] G := ⟨(ULift.moduleEquiv (R := ℂ) (M := E)).symm.toLinearMap, hupcont⟩
    have hGdense := hforall G hGadd hGmod hGunif hGuadd hGpolyn hGT2
    have hdmem : downCLM ∈ closure (X := PrecompactConvergenceCLM G E)
        (range (fun z ↦ tensorToFiniteRank z)) := hGdense downCLM
    obtain ⟨zG, hzG⟩ :=
      (mem_closure_finiteRank_iff E downCLM).mp hdmem (hupCLM '' B) (hB.image hupCLM.uniformContinuous) V hV
    exact ⟨TensorProduct.map
      { toFun := fun ψ : StrongDual ℂ G => ψ.comp hupCLM
        map_add' := fun ψ χ => by ext y; rfl
        map_smul' := fun c ψ => by ext y; rfl }
      (LinearMap.id : E →ₗ[ℂ] E) zG, fun x hx ↦ by
      rw [tensorToFiniteRank_precomp_apply]
      exact hzG (hupCLM x) (mem_image_of_mem hupCLM hx)⟩

/-- For each continuous seminorm of a nuclear space, the map to its Banach
completion sends some zero-neighborhood into a compact set. -/
private theorem isCompactOperator_localBanach_coe (hE : IsNuclearTVS.{v, u} E)
    (q : Seminorm ℂ E) (hq : Continuous q) :
    IsCompactOperator (fun x : E ↦ ((show WithLocalSeminorm q from x) : LocalBanach q)) := by
  classical
  let U := q.ball 0 1
  have hU : U ∈ 𝓝 (0 : E) := q.ball_mem_nhds hq one_pos
  have bU : Balanced ℂ U := q.balanced_ball_zero 1
  have cU : Convex ℝ U := q.convex_ball 0 1
  obtain ⟨V, hV, bV, cV, hVU, C, hC, hsum⟩ :=
    exists_localBanachMap_absolutelySumming E hE U hU bU cU
  let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
  let q' := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
  let T := localBanachMap p q' (gauge_mono (absorbent_nhds_zero hV) hVU)
  have hq' : q' = q := DFunLike.coe_injective (q.restrictScalars ℝ).gauge_ball
  have hp : Continuous p := continuous_gauge cV hV
  obtain ⟨j, hj⟩ := exists_localBanach_inclusion p hp
  obtain ⟨H, _, _, _, a, D, hD, ha⟩ := exists_hilbert_domination hE p hp
  -- Extend the map into the source local Banach space across the Hilbert closure.
  let R := LinearMap.range a.toLinearMap
  let a' : E →L[ℂ] R.topologicalClosure :=
    a.codRestrict _ fun x ↦ R.le_topologicalClosure ⟨x, rfl⟩
  let : CompleteSpace R.topologicalClosure := R.isClosed_topologicalClosure.completeSpace_coe
  have hd : DenseRange a' := by
    change DenseRange (Set.inclusion (s := (R : Set H))
      (R.le_topologicalClosure : (R : Set H) ⊆ R.topologicalClosure) ∘ Set.rangeFactorization a)
    exact ((denseRange_inclusion_iff _).mpr subset_rfl).comp
      Set.rangeFactorization_surjective.denseRange (continuous_inclusion _)
  have hj' (x : E) : ‖j x‖ ≤ D * ‖a' x‖ := by
    rw [hj, localBanach_norm_coe]
    exact ha x
  let A := j.toLinearMap.extendOfNorm a'.toLinearMap
  have hA (x : E) : A (a' x) = j x := LinearMap.extendOfNorm_eq hd ⟨D, hj'⟩ x
  have hAnorm : ‖A‖ ≤ D := LinearMap.opNorm_extendOfNorm_le hd hD hj'
  -- Absolute summability is preserved by precomposition with the extended map.
  let K := T.comp A
  have hK : IsCompactOperator K := by
    apply isCompactOperator_of_hilbert_absolutelySumming K (C := C * (D + 1)) (by positivity)
    intro n x M hM hx
    have hpos : 0 < D + 1 := by positivity
    have hweak (φ : LocalBanach p →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) :
        ∑ i, ‖φ (A (x i))‖ ≤ (D + 1) * M := by
      let r : ℂ := ((D + 1 : ℝ) : ℂ)
      have hr : ‖r‖ = D + 1 := Complex.norm_of_nonneg hpos.le
      let ψ := r⁻¹ • φ.comp A
      have hψ : ‖ψ‖ ≤ 1 := by
        rw [norm_smul, norm_inv, hr, inv_mul_le_iff₀ hpos, mul_one]
        exact (φ.opNorm_comp_le A).trans
          ((mul_le_of_le_one_left (norm_nonneg A) hφ).trans (by linarith))
      have hψi (i : Fin n) : ‖ψ (x i)‖ = (D + 1)⁻¹ * ‖φ (A (x i))‖ := by
        simp only [ψ, smul_apply, norm_smul, norm_inv, hr,
          ContinuousLinearMap.comp_apply]
      have h := hx ψ hψ
      rw [Finset.sum_congr rfl (fun i _ ↦ hψi i), ← Finset.mul_sum] at h
      exact (inv_mul_le_iff₀ hpos).mp h
    simpa only [K, ContinuousLinearMap.comp_apply, mul_assoc] using
      hsum n (fun i ↦ A (x i)) ((D + 1) * M) (mul_nonneg hpos.le hM) hweak
  let J : E → LocalBanach q' := fun x ↦ (show WithLocalSeminorm q' from x)
  have hJ : J = K ∘ a' := by
    funext x
    change J x = T (A (a' x))
    rw [hA, hj]
    exact (localBanachMap_coe p q' _ (show WithLocalSeminorm p from x)).symm
  rw [← hq']
  change IsCompactOperator J
  rw [hJ]
  exact hK.comp_clm a'

/-- Paper: Lemma C.2.4.16(1), p. 690. A bounded set in a nuclear space has
compact closure in the completion. -/
theorem isPrecompactInCompletion_of_isNuclearTVS (hE : IsNuclearTVS.{v, u} E)
    {S : Set E} (hS : IsVonNBounded ℂ S) : IsPrecompactInCompletion S := by
  classical
  apply (isPrecompactInCompletion_iff_totallyBounded S).mpr
  refine (PolynormableSpace.hasBasis_zero_ball ℂ E).uniformity_of_nhds_zero.totallyBounded_iff.mpr ?_
  intro q hq
  obtain ⟨j, hj⟩ := exists_localBanach_inclusion q hq
  have hc : IsCompactOperator j := (funext hj).symm ▸ isCompactOperator_localBanach_coe E hE q hq
  obtain ⟨B, hB, hsub⟩ := hc.image_subset_compact_of_isVonNBounded (f := j.toLinearMap) hS
  have htotal := hB.totallyBounded.subset hsub
  -- Lift the centers of a finite net back to the bounded set.
  obtain ⟨s, hs, hsf, hcover⟩ := htotal.exists_subset (Metric.dist_mem_uniformity one_pos)
  have hpre (y : s) : ∃ x : E, x ∈ S ∧ j x = y := hs y.property
  choose g hg using hpre
  let : Finite s := hsf.to_subtype
  refine ⟨range g, finite_range g, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover (mem_image_of_mem j hx))
  refine mem_iUnion₂.mpr ⟨g ⟨y, hy⟩, mem_range_self _, ?_⟩
  change dist (j x) y < 1 at hxy
  have hy' : j (g ⟨y, hy⟩) = y := (hg ⟨y, hy⟩).2
  rw [← hy', dist_comm, dist_eq_norm] at hxy
  change g ⟨y, hy⟩ - x ∈ q.ball 0 1
  apply q.mem_ball_zero.mpr
  rw [hj, hj] at hxy
  let x' : WithLocalSeminorm q := x
  let y' : WithLocalSeminorm q := g ⟨y, hy⟩
  change q (y' - x') < 1
  rw [← localBanach_norm_coe q (y' - x'), Completion.coe_sub]
  exact hxy

/-- Paper: Lemma C.2.4.16(1), p. 690. For a nuclear source, uniform convergence
on bounded sets and on precompact sets give the same topology on the operator space. -/
theorem precompactConvergenceCLM_eq_bounded_of_isNuclearTVS (hE : IsNuclearTVS.{v, u} E)
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [PolynormableSpace ℂ F] [T2Space F] :
    (inferInstance : TopologicalSpace (PrecompactConvergenceCLM E F)) =
      (inferInstance : TopologicalSpace (E →L[ℂ] F)) := by
  have hsets : {S : Set E | IsPrecompactInCompletion S} = {S | IsVonNBounded ℂ S} := by
    ext S
    exact ⟨fun hS ↦ ((isPrecompactInCompletion_iff_totallyBounded S).mp hS).isVonNBounded ℂ,
      isPrecompactInCompletion_of_isNuclearTVS E hE⟩
  let convergenceTopology (S : Set (Set E)) : TopologicalSpace (E →L[ℂ] F) :=
    UniformConvergenceCLM.instTopologicalSpace (RingHom.id ℂ) F S
  exact congrArg convergenceTopology hsets

/-- Paper: Lemma C.2.4.16(2), p. 690. Finite-rank endomorphisms of a nuclear
space are dense for uniform convergence on precompact sets. -/
theorem dense_finiteRank_of_isNuclearTVS (hE : IsNuclearTVS.{v, u} E) :
    HasApproximationProperty E := by
  classical
  apply (id_mem_closure_finiteRank_iff_dense E).mp
  refine (mem_closure_finiteRank_iff E (ContinuousLinearMap.id ℂ E)).mpr ?_
  intro B hB V hV
  obtain ⟨q, hq, hqV⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hV
  obtain ⟨H, _, _, _, a, C, hC, ha⟩ := exists_hilbert_domination hE q hq
  let ε : ℝ := (C + 1)⁻¹
  have hpos : 0 < C + 1 := by positivity
  -- Take the net inside the image so its span has basis vectors that lift to E.
  obtain ⟨s, hs, hsf, hcover⟩ :=
    (hB.image a.uniformContinuous).exists_subset (Metric.dist_mem_uniformity (inv_pos.mpr hpos))
  let W := Submodule.span ℂ s
  let : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ hsf
  let b := stdOrthonormalBasis ℂ W
  have hW : W ≤ a.toLinearMap.range := Submodule.span_le.mpr fun y hy ↦ by
    obtain ⟨x, _, rfl⟩ := hs hy
    exact ⟨x, rfl⟩
  choose lift hlift using fun i ↦ (show ∃ x, a x = (b i : H) from hW (b i).property)
  let φ i : StrongDual ℂ E := (innerSL ℂ (b i : H)).comp a
  let z : StrongDual ℂ E ⊗[ℂ] E := ∑ i, φ i ⊗ₜ[ℂ] lift i
  have hproj (x : E) : a (tensorToFiniteRank z x) = W.starProjection (a x) := by
    rw [b.starProjection_eq_sum_rankOne]
    simp only [z, map_sum, sum_apply, tensorToFiniteRank_tmul, map_smul, hlift, φ,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, InnerProductSpace.rankOne_apply]
  refine ⟨z, fun x hx ↦ hqV (q.mem_ball_zero.mpr ?_)⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover (mem_image_of_mem a hx))
  have hdist : dist (a x) (W.starProjection (a x)) < ε := by
    rw [W.dist_starProjection_eq_infDist]
    exact (Metric.infDist_le_dist_of_mem (Submodule.subset_span hy : y ∈ W)).trans_lt hxy
  change q (tensorToFiniteRank z x - x) < 1
  calc
    _ ≤ C * ‖a (tensorToFiniteRank z x - x)‖ := ha _
    _ = C * dist (a x) (W.starProjection (a x)) := by
      rw [map_sub, hproj, dist_comm, dist_eq_norm]
    _ ≤ C * ε := mul_le_mul_of_nonneg_left hdist.le hC
    _ < 1 := (mul_inv_lt_iff₀ hpos).mpr (by linarith)

/-- Paper: Remark C.2.4.17, p. 690. For a nuclear source, finite-rank maps are
dense in the strong operator space with uniform convergence on bounded sets. -/
theorem dense_finiteRank_boundedConvergence_of_isNuclearTVS (hE : IsNuclearTVS.{v, u} E)
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [PolynormableSpace ℂ F] [T2Space F] :
    DenseRange (tensorToFiniteRank (E := E) (F := F)) := by
  intro A
  let S := {s : Set E | IsVonNBounded ℂ s}
  let post : (E →Lᵤ[ℂ, S] E) →L[ℂ] (E →Lᵤ[ℂ, S] F) := A.postcompUniformConvergenceCLM S
  have hd := (dense_finiteRank_of_isNuclearTVS E hE) (ContinuousLinearMap.id ℂ E)
  let approximable (t : TopologicalSpace (E →L[ℂ] E)) :=
    ContinuousLinearMap.id ℂ E ∈ @closure _ t (range (tensorToFiniteRank (E := E) (F := E)))
  have hb := (congrArg approximable
    (precompactConvergenceCLM_eq_bounded_of_isNuclearTVS E hE E)).mp hd
  have hsub : post '' range (fun z ↦ tensorToFiniteRank z) ⊆
      range (tensorToFiniteRank (E := E) (F := F)) := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨TensorProduct.map LinearMap.id A.toLinearMap z, ?_⟩
    ext x
    change tensorToFiniteRank _ x = A (tensorToFiniteRank z x)
    induction z using TensorProduct.inductionOn with
    | tmul φ y => simp [tensorToFiniteRank_tmul]
    | add z w hz hw => simp only [map_add, add_apply, hz, hw]
  exact closure_mono hsub (image_closure_subset_closure_image post.continuous
    (mem_image_of_mem post hb))

/-- Paper: Remark C.2.4.17, p. 690. Bounded subsets of a quasi-complete nuclear
space have compact closure in the space itself. -/
theorem isCompact_closure_of_isNuclearTVS [QuasiCompleteSpace ℂ E]
    (hE : IsNuclearTVS.{v, u} E) {S : Set E} (hS : IsVonNBounded ℂ S) :
    IsCompact (closure S) := by
  have h := (isPrecompactInCompletion_iff_totallyBounded S).mp
    (isPrecompactInCompletion_of_isNuclearTVS E hE hS)
  exact h.closure.isCompact_of_isComplete
    (QuasiCompleteSpace.quasiComplete hS.closure isClosed_closure)

end ApproximationProperty

section StrongDualNuclearity

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

open scoped BoundedContinuousFunction

/-- Restriction to a bounded set takes continuous functionals to bounded continuous functions. -/
private def restrictDualToBounded {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (B : Set E) (hB : IsVonNBounded ℂ B) : StrongDual ℂ E →ₗ[ℂ] (B →ᵇ ℂ) where
  toFun φ := by
    let h := (NormedSpace.image_isVonNBounded_iff ℂ).mp (hB.image φ)
    exact BoundedContinuousFunction.ofNormedAddCommGroup (fun x : B ↦ φ x)
      (φ.continuous.comp continuous_subtype_val) h.choose (fun x ↦ h.choose_spec x x.property)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Evaluating the function factor of a tensor at a point of the bounded set. -/
private def evalBoundedTensor {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [T2Space E] {B : Set E} (x : B) :
    ProjectiveTensor E (B →ᵇ ℂ) →L[ℂ] E := by
  let := PolynormableSpace.isTopologicalAddGroup ℂ E
  let := PolynormableSpace.continuousSMul ℂ E
  let Y := B →ᵇ ℂ
  let T := TensorProduct.lift (LinearMap.mk₂ ℂ (fun (v : E) (g : Y) ↦ g x • v)
    (fun _ _ _ ↦ smul_add _ _ _) (fun _ _ _ ↦ smul_comm _ _ _)
    (fun _ _ _ ↦ add_smul _ _ _) (fun _ _ _ ↦ mul_smul _ _ _))
  refine ⟨T, (continuous_projectiveTensor_iff (E := E) (F := Y) T).mpr ?_⟩
  exact ((continuous_eval_const x).comp (continuous_snd : Continuous (Prod.snd : E × Y → Y))).smul
    continuous_fst

/-- Finite-rank approximations to the identity on a bounded set give a single completed
tensor whose function factor evaluates to the inclusion at each point. -/
private theorem exists_tensor_of_bounded_inclusion {E : Type u} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    [FirstCountableTopology E] [CompleteSpace E] (hN : IsNuclearTVS.{v} E)
    (B : Set E) (hB : IsVonNBounded ℂ B) :
    ∃ z : Completion (ProjectiveTensor E (B →ᵇ ℂ)), ∀ x : B,
      (evalBoundedTensor x).fromCompletion z = x := by
  classical
  let Y := B →ᵇ ℂ
  let P := ProjectiveTensor E Y
  let S := equicontinuousCompactology E
  let res := restrictDualToBounded B hB
  let lift := (TensorProduct.map LinearMap.id res).comp (TensorProduct.comm ℂ (StrongDual ℂ E) E).toLinearMap
  have hcontract (z : StrongDual ℂ E ⊗[ℂ] E) (φ : WeakDual ℂ E) (x : B) :
      tensorDualOperator (lift z) φ.toStrongDual x = φ (tensorToFiniteRank z x) := by
    induction z using TensorProduct.inductionOn with
    | tmul f y =>
      change φ y * f x = φ (f x • y)
      rw [map_smul, smul_eq_mul, mul_comm]
    | add z w hz hw => simpa only [map_add, LinearMap.add_apply, add_apply] using congrArg₂ (· + ·) hz hw
  have heval (z : StrongDual ℂ E ⊗[ℂ] E) (x : B) :
      evalBoundedTensor x (lift z) = tensorToFiniteRank z x := by
    let ev : E ⊗[ℂ] Y →ₗ[ℂ] E := (evalBoundedTensor x).toLinearMap
    change ev (lift z) = _
    induction z using TensorProduct.inductionOn with
    | tmul f y => rfl
    | add z w hz hw => simpa only [map_add, add_apply] using congrArg₂ (· + ·) hz hw
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  have ht := (isPrecompactInCompletion_iff_totallyBounded B).mp
    (isPrecompactInCompletion_of_isNuclearTVS E hN hB)
  have happrox := (mem_closure_finiteRank_iff E (ContinuousLinearMap.id ℂ E)).mp
    ((dense_finiteRank_of_isNuclearTVS E hN) (ContinuousLinearMap.id ℂ E)) B ht
  choose z hz using fun n ↦ happrox (U n) (hU.1.mem_of_mem (i := n) trivial)
  let seq (n : ℕ) : P := lift (z n)
  let J₀ : (E ⊗[ℂ] Y) →+ (WeakDual ℂ E →ᵤ[S] Y) :=
    { toFun := fun t ↦ UniformOnFun.ofFun S (fun φ ↦ tensorDualOperator t φ.toStrongDual)
      map_zero' := funext fun φ ↦ by
        change tensorDualOperator (0 : E ⊗[ℂ] Y) φ.toStrongDual = 0
        rw [map_zero, LinearMap.zero_apply]
      map_add' := fun t s ↦ funext fun φ ↦ by
        change tensorDualOperator (t + s : E ⊗[ℂ] Y) _ = _; rw [map_add]; rfl }
  let J : P →+ (WeakDual ℂ E →ᵤ[S] Y) := J₀
  have hn : IsNuclearTVS.{0} E := (isNuclearTVS_iff_localBanach_integral E).mpr
    ((isNuclearTVS_iff_localBanach_integral E).mp hN)
  have hJ : IsUniformInducing J := AddMonoidHom.isUniformInducing_of_isInducing
    ((tensorDualOperator_isEmbedding (E := E) (Y := Y)).isInducing.comp
      (hn.2.2 Y inferInstance inferInstance inferInstance inferInstance inferInstance).isInducing)
  have hconv : Tendsto (J ∘ seq) atTop
      (𝓝 (UniformOnFun.ofFun S (fun φ : WeakDual ℂ E ↦ res φ.toStrongDual))) := by
    apply UniformOnFun.tendsto_iff_tendstoUniformlyOn.mpr
    intro A hA
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨m, _, hm⟩ := hU.1.mem_iff.mp
      (Metric.equicontinuousAt_iff_right.mp hA.1 (ε / 2) (half_pos hε))
    filter_upwards [eventually_ge_atTop m] with n hn φ hφ
    rw [dist_comm, dist_eq_norm]
    refine lt_of_le_of_lt ((BoundedContinuousFunction.norm_le (half_pos hε).le).mpr fun x ↦ ?_)
      (half_lt_self hε)
    have h := hm (hU.antitone hn (hz n x x.property)) (⟨φ, hφ⟩ : A)
    change ‖tensorDualOperator (lift (z n)) φ.toStrongDual x - φ x‖ ≤ _
    rw [hcontract, ← map_sub]
    simpa only [map_zero, dist_zero_left, ContinuousLinearMap.id_apply] using h.le
  have hC : CauchySeq seq := hJ.cauchy_map_iff.mp (by
    rw [Filter.map_map]; exact hconv.cauchySeq)
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete ((Completion.uniformContinuous_coe P).comp_cauchySeq hC)
  refine ⟨w, fun x ↦ tendsto_nhds_unique (((evalBoundedTensor x).fromCompletion.continuous.tendsto w).comp hw) ?_⟩
  have hx : Tendsto (fun n ↦ tensorToFiniteRank (z n) x - (x : E)) atTop (𝓝 0) := by
    apply hU.1.tendsto_right_iff.mpr
    intro m _
    exact (eventually_ge_atTop m).mono fun n hn ↦ hU.antitone hn (hz n x x.property)
  have ht := hx.add (tendsto_const_nhds (x := (x : E)) (f := atTop))
  have ht' : Tendsto (fun n ↦ tensorToFiniteRank (z n) x) atTop (𝓝 (x : E)) := by
    simpa only [zero_add, sub_add_cancel] using ht
  apply ht'.congr
  intro n
  change tensorToFiniteRank (z n) x = (evalBoundedTensor x).fromCompletion (↑(seq n) : Completion P)
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  exact (heval (z n) x).symm

/-- Paper: Lemma C.2.4.11, p. 689. In a nuclear Fréchet space, each bounded set is
contained in the set of sums of an absolutely weighted bounded sequence, with
coefficients in the complex unit disk. This is the bounded-set step of dual nuclearity.
Finite-rank approximations to the inclusion converge uniformly on the bounded set.
Their tensor limit has a series expansion whose point evaluations cover the set. -/
theorem exists_bounded_series_cover_of_nuclear_frechet
    (hE : IsFrechetTVS E) (hN : IsNuclearTVS.{v, u} E) (B : Set E) (hB : IsVonNBounded ℂ B) :
    ∃ (c : ℕ → ℂ) (x : ℕ → E), Summable (fun k ↦ ‖c k‖) ∧ IsVonNBounded ℂ (range x) ∧
      ∀ y ∈ B, ∃ a : ℕ → ℂ, (∀ k, ‖a k‖ ≤ 1) ∧
        HasSum (fun k ↦ (c k * a k) • x k) y := by
  obtain ⟨hadd, hpoly, hmet, hcomplete⟩ := hE
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let Y := B →ᵇ ℂ
  obtain ⟨z, hz⟩ := exists_tensor_of_bounded_inclusion hN B hB
  obtain ⟨c, x, g, hc, hx, hg, hs⟩ := completedProjectiveTensor_exists_series
    ⟨hadd, hpoly, hmet, hcomplete⟩ (isFrechetTVS_of_banach Y) z
  obtain ⟨M, hM⟩ := (show Tendsto (fun n ↦ ‖g n‖) atTop (𝓝 0) by simpa using hg.norm).bddAbove_range
  let k : ℂ := (max 1 M : ℝ)
  have hk : 0 < max 1 M := zero_lt_one.trans_le (le_max_left _ _)
  have hnorm : ‖k‖ = max 1 M := Complex.norm_of_nonneg hk.le
  have hk0 : k ≠ 0 := norm_pos_iff.mp (hnorm ▸ hk)
  refine ⟨c, fun n ↦ k • x n, hc, ?_, fun y hy ↦ ?_⟩
  · apply Filter.Tendsto.isVonNBounded_range ℂ (x := 0)
    simpa using hx.const_smul k
  · let b : B := ⟨y, hy⟩
    refine ⟨fun n ↦ g n b / k, fun n ↦ ?_, ?_⟩
    · rw [norm_div, hnorm, div_le_one hk]
      exact ((g n).norm_coe_le_norm b).trans ((hM (mem_range_self n)).trans (le_max_right _ _))
    · rw [← show (evalBoundedTensor b).fromCompletion z = y from hz b]
      refine (hs.map (evalBoundedTensor b).fromCompletion (evalBoundedTensor b).fromCompletion.continuous).congr_fun ?_
      intro n
      change (c n * ((g n) b / k)) • k • x n =
        (evalBoundedTensor b).fromCompletion (Completion.coe' (α := ProjectiveTensor E Y) _)
      let v : ProjectiveTensor E Y := x n ⊗ₜ[ℂ] g n
      change _ = (evalBoundedTensor b).fromCompletion (↑(c n • v) : Completion (ProjectiveTensor E Y))
      rw [ContinuousLinearMap.fromCompletion_apply_coe, map_smul, smul_smul]
      change _ = c n • (g n b) • x n
      rw [smul_smul]
      congr 1
      field_simp

/-- Paper: Lemma C.2.4.11, p. 689. A Fréchet space is nuclear exactly when its
strong dual is nuclear. -/
theorem isNuclearTVS_strongDual_iff (hE : IsFrechetTVS E) :
    IsNuclearTVS.{v, u} (StrongDual ℂ E) ↔ IsNuclearTVS.{v, u} E := by
  obtain ⟨hadd, hpoly, hmet, hcomplete⟩ := hE
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : ContinuousSMul ℂ E := PolynormableSpace.continuousSMul ℂ E
  constructor
  · intro h
    exact isNuclearTVS_of_signedSum_bound fun q hq ↦
      exists_sum_bound_on_nhds_of_bounded q
        (exists_sum_bound_on_bounded_sets_of_isNuclearTVS_strongDual h q hq)
  · intro h
    exact isNuclearTVS_strongDual_of_bounded_series_cover
      (exists_bounded_series_cover_of_nuclear_frechet ⟨hadd, hpoly, hmet, hcomplete⟩ h)

end StrongDualNuclearity

/-- Pulling back a bounded family of Banach-space functionals gives one continuous
seminorm bounding every member of the resulting family. -/
private theorem exists_seminorm_bound_comp {X H : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (j : X →L[ℂ] H) (φ : ℕ → StrongDual ℂ H) (hφ : Tendsto φ atTop (𝓝 0)) :
    ∃ p : Seminorm ℂ X, Continuous p ∧ ∀ n x, ‖φ n (j x)‖ ≤ p x := by
  obtain ⟨A, hA⟩ := (show Tendsto (fun n ↦ ‖φ n‖) atTop (𝓝 0) by simpa using hφ.norm).bddAbove_range
  let q := (normSeminorm ℂ H).comp j.toLinearMap
  have hq : Continuous q := j.continuous.norm
  refine ⟨A.toNNReal • q, hq.const_smul A.toNNReal, fun n x ↦ ?_⟩
  exact ((φ n).le_opNorm _).trans (mul_le_mul_of_nonneg_right
    ((hA (mem_range_self n)).trans (Real.le_coe_toNNReal A)) (norm_nonneg _))

private theorem equicontinuousAt_of_seminorm_bound {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (φ : ℕ → StrongDual ℂ X) (p : Seminorm ℂ X) (hp : Continuous p)
    (h : ∀ n x, ‖φ n x‖ ≤ p x) : EquicontinuousAt (fun n ↦ (φ n : X → ℂ)) 0 := by
  apply Metric.equicontinuousAt_iff_right.mpr
  intro ε hε
  filter_upwards [p.ball_mem_nhds hp hε] with x hx n
  simpa only [map_zero, dist_zero_left] using (h n x).trans_lt (p.mem_ball_zero.mp hx)

/-- Paper: Theorem C.2.4.18, p. 690. A jointly continuous bilinear form with
nuclear first factor is an absolutely weighted sum of products of two equicontinuous
sequences of functionals. The series converges uniformly on bounded sets in the product.
Deviation: The second pairing in (C.2.4.8) uses the second space and its dual. -/
theorem schwartz_kernel_series {E : Type u} {F : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
    (hE : IsNuclearTVS.{v, u} E) (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)
    (hB : Continuous (fun z : E × F ↦ B z.1 z.2)) :
    ∃ (φ : ℕ → StrongDual ℂ E) (ψ : ℕ → StrongDual ℂ F) (c : ℕ → ℂ),
      EquicontinuousAt (fun n : ℕ ↦ (φ n : E → ℂ)) 0 ∧
      EquicontinuousAt (fun n : ℕ ↦ (ψ n : F → ℂ)) 0 ∧ Summable (fun n ↦ ‖c n‖) ∧
      let S := {A : Set (E × F) | IsVonNBounded ℂ A}
      HasSum (fun n ↦ UniformOnFun.ofFun S (fun z : E × F ↦ c n * φ n z.1 * ψ n z.2))
        (UniformOnFun.ofFun S (fun z : E × F ↦ B z.1 z.2)) := by
  let := PolynormableSpace.isTopologicalAddGroup ℂ E
  let := PolynormableSpace.isTopologicalAddGroup ℂ F
  let r := (normSeminorm ℂ ℂ).comp (TensorProduct.lift B)
  obtain ⟨q, s, hq, hs, hrs⟩ := exists_projectiveSeminorm_pure_bound E r hB.norm.continuousAt
  let U := q.ball 0 1
  have hU : U ∈ 𝓝 (0 : E) := q.ball_mem_nhds hq one_pos
  obtain ⟨V, hV, bV, cV, hVU, c, φ, b, hc, hφ, hb, hseries⟩ :=
    (isNuclearTVS_iff_localBanach_series E).mp hE U hU (q.balanced_ball_zero 1) (q.convex_ball 0 1)
  let p := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
  let q' := gaugeSeminorm (q.balanced_ball_zero 1) (q.convex_ball 0 1) (absorbent_nhds_zero hU)
  have hq' : q' = q := DFunLike.coe_injective (q.restrictScalars ℝ).gauge_ball
  obtain ⟨j, hj⟩ := exists_localBanach_inclusion p (continuous_gauge cV hV)
  obtain ⟨k, hk⟩ := exists_localBanach_inclusion s hs
  -- Extend the bilinear form to both seminorm completions.
  let B₀ : WithLocalSeminorm q' →L[ℂ] WithLocalSeminorm s →L[ℂ] ℂ :=
    (show WithLocalSeminorm q' →ₗ[ℂ] WithLocalSeminorm s →ₗ[ℂ] ℂ from B).mkContinuous₂ 1
      (fun x y ↦ by
        change ‖B x y‖ ≤ 1 * q' x * s y
        rw [one_mul, hq']
        exact hrs x y)
  let D := B₀.fromCompletion.flip.fromCompletion.flip
  let Φ (n : ℕ) := (φ n).comp j
  let Ψ (n : ℕ) := (D (b n)).comp k
  have hval (x : E) (y : F) :
      HasSum (fun n ↦ c n * Φ n x * Ψ n y) (B x y) := by
    have hle : q' ≤ p := gauge_mono (absorbent_nhds_zero hV) hVU
    have he : D (localBanachMap p q' hle (j x)) (k y) = B x y := by
      rw [hj, hk, localBanachMap_coe]
      let x' : WithLocalSeminorm q' := x
      let y' : WithLocalSeminorm s := y
      change B₀.fromCompletion.flip.fromCompletion (y' : LocalBanach s) (x' : LocalBanach q') = B x y
      rw [ContinuousLinearMap.fromCompletion_apply_coe, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.fromCompletion_apply_coe]
      rfl
    rw [← he]
    exact ((hseries (j x)).map (D.flip (k y)) (D.flip (k y)).continuous).congr_fun
      (fun n ↦ by
        change _ = D.flip (k y) ((c n * φ n (j x)) • b n)
        rw [map_smul]
        rfl)
  obtain ⟨P, hP, hΦ⟩ := exists_seminorm_bound_comp j φ hφ
  have hDb : Tendsto (fun n ↦ D (b n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using (D.continuous.tendsto 0).comp hb
  obtain ⟨Q, hQ, hΨ⟩ := exists_seminorm_bound_comp k _ hDb
  refine ⟨Φ, Ψ, c, equicontinuousAt_of_seminorm_bound Φ P hP hΦ,
    equicontinuousAt_of_seminorm_bound Ψ Q hQ hΨ, hc, ?_⟩
  apply UniformOnFun.tendsto_iff_tendstoUniformlyOn.mpr
  intro A hA
  obtain ⟨M, hM, hm⟩ := (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mp
    (hA.image (ContinuousLinearMap.fst ℂ E F)) ⟨P, hP⟩
  obtain ⟨N, hN, hn⟩ := (PolynormableSpace.withSeminorms ℂ F).isVonNBounded_iff_seminorm_bounded.mp
    (hA.image (ContinuousLinearMap.snd ℂ E F)) ⟨Q, hQ⟩
  let term (n : ℕ) (z : E × F) := c n * Φ n z.1 * Ψ n z.2
  have hmajor (n) (z : E × F) (hz : z ∈ A) : ‖term n z‖ ≤ ‖c n‖ * M * N := by
    simp only [term, norm_mul]
    gcongr
    · exact (hΦ n z.1).trans (hm _ (mem_image_of_mem _ hz)).le
    · exact (hΨ n z.2).trans (hn _ (mem_image_of_mem _ hz)).le
  have hu := (tendstoUniformlyOn_tsum ((hc.mul_right M).mul_right N) hmajor).congr_right
    (fun z _ ↦ (hval z.1 z.2).tsum_eq)
  change TendstoUniformlyOn (fun t : Finset ℕ ↦ ∑ n ∈ t, term n)
    (fun z ↦ B z.1 z.2) atTop A
  exact hu.congr (Eventually.of_forall fun t z _ ↦ (Finset.sum_apply z t term).symm)

-- TODO(paper-gap): After (C.2.4.9), continuity into the strong dual need not imply
-- joint continuity of the associated form, even for a complete nuclear space.
-- TODO(later): needs §D.1.4–D.1.5 for the Schwartz–Bruhat spaces in Theorem C.2.4.19.

/-! ## The finest locally convex topology -/

section FinestLocallyConvex

variable (E : Type u) [AddCommGroup E] [Module ℂ E]

/-- Paper: Proposition C.2.5.1(1), p. 691. The vector space with its finest locally
convex topology is the type synonym generated by all seminorms on the carrier. -/
abbrev FinestLocallyConvex := WithGeneratingSeminorms E (id : Seminorm ℂ E → Seminorm ℂ E)

/-- Paper: Proposition C.2.5.1(1), p. 691. All seminorms generate the finest locally
convex topology. -/
theorem finestLocallyConvex_withSeminorms :
    WithSeminorms (E := FinestLocallyConvex E) (id : Seminorm ℂ E → Seminorm ℂ E) :=
  withGeneratingSeminorms_spec E _

/-- Paper: Proposition C.2.5.1(1), p. 691. The finest locally convex topology is
Hausdorff.
Deviation: The Hausdorff property is used throughout the proposition. -/
theorem finestLocallyConvex_t2 : T2Space (FinestLocallyConvex E) := by
  have hp := finestLocallyConvex_withSeminorms E
  have := hp.isTopologicalAddGroup
  have : T1Space (FinestLocallyConvex E) := hp.T1_of_separating fun x hx ↦ by
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ (V := E) hx
    refine ⟨(normSeminorm ℂ ℂ).comp f, ?_⟩
    change ‖f x‖ ≠ 0
    exact norm_ne_zero_iff.mpr hf
  infer_instance

/-- Paper: Proposition C.2.5.1(1), p. 691. The topology generated by all seminorms
equals the final locally convex topology of the inclusions of finite-dimensional
subspaces, each with its unique Hausdorff vector topology. -/
theorem finestLocallyConvex_eq_finiteDimensionalFinalTopology :
    (inferInstance : TopologicalSpace (FinestLocallyConvex E)) =
      locallyConvexFinalTopology
        (X := fun S : {S : Submodule ℂ E // FiniteDimensional ℂ S} ↦ FinestLocallyConvex S.val)
        (fun S ↦ S.val.subtype) := by
  have hcont (p : Seminorm ℂ E) (S : {S : Submodule ℂ E // FiniteDimensional ℂ S}) :
      Continuous (fun x : FinestLocallyConvex S.val ↦ p (S.val.subtype x)) :=
    (finestLocallyConvex_withSeminorms S.val).continuous_seminorm (p.comp S.val.subtype)
  exact ((finestLocallyConvex_withSeminorms E).congr_equiv
    (Equiv.subtypeUnivEquiv hcont)).withSeminorms_eq

/-- Paper: Proposition C.2.5.1(2), p. 691. Every linear map from a space with
the finest locally convex topology to a Hausdorff locally convex space is continuous. -/
theorem continuous_of_finestLocallyConvex {M : Type*} [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace M] [PolynormableSpace ℂ M] [T2Space M]
    (T : FinestLocallyConvex E →ₗ[ℂ] M) : Continuous T := by
  have hp := finestLocallyConvex_withSeminorms E
  have := hp.isTopologicalAddGroup
  exact (PolynormableSpace.withSeminorms ℂ M).continuous_of_continuous_comp T fun q ↦
    hp.continuous_seminorm (q.1.comp T)

/-- Paper: Proposition C.2.5.1(2), p. 691. Every algebraic functional on the
space with its finest locally convex topology belongs to the continuous dual. -/
theorem finestLocallyConvex_dual_surjective :
    Function.Surjective (fun φ : StrongDual ℂ (FinestLocallyConvex E) ↦ φ.toLinearMap) :=
  fun l ↦ ⟨⟨l, continuous_of_finestLocallyConvex E l⟩, rfl⟩

variable {E}

/-- Paper: Proposition C.2.5.1(3), p. 691. Every linear subspace of a space with
the finest locally convex topology is closed. -/
theorem finestLocallyConvex_submodule_isClosed (S : Submodule ℂ (FinestLocallyConvex E)) :
    IsClosed (S : Set (FinestLocallyConvex E)) := by
  have hS : (S : Set (FinestLocallyConvex E)) =
      ⋂ φ ∈ S.dualAnnihilator, {x | φ x = 0} := by
    ext x
    simp only [SetLike.mem_coe, mem_iInter, Submodule.mem_dualAnnihilator, mem_ofPred_eq]
    refine ⟨fun hx φ hφ ↦ hφ x hx, fun h ↦ ?_⟩
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := S), Submodule.mem_dualCoannihilator]
    exact fun φ hφ ↦ h φ ((Submodule.mem_dualAnnihilator φ).mp hφ)
  rw [hS]
  exact isClosed_biInter fun φ _ ↦
    isClosed_eq (continuous_of_finestLocallyConvex E φ) continuous_const

/-- Paper: Proposition C.2.5.1(3), p. 691. Every linear subspace is the image
of a continuous linear projection that restricts to the identity on the subspace. -/
theorem finestLocallyConvex_submodule_closedComplemented
    (S : Submodule ℂ (FinestLocallyConvex E)) : S.ClosedComplemented := by
  have := finestLocallyConvex_t2 E
  obtain ⟨q, hq⟩ := S.exists_isCompl
  let P := Submodule.projectionOnto S q hq
  exact ⟨⟨P, continuous_of_finestLocallyConvex E P⟩, Submodule.projectionOnto_apply_left hq⟩

/-- Paper: Proposition C.2.5.1(3), p. 691. A linear subspace inherits its own
finest locally convex topology. -/
theorem finestLocallyConvex_submodule_topology (S : Submodule ℂ (FinestLocallyConvex E)) :
    (inferInstance : TopologicalSpace S) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex S)) := by
  have := finestLocallyConvex_t2 E
  have := finestLocallyConvex_t2 S
  have : PolynormableSpace ℂ (FinestLocallyConvex S) := inferInstance
  obtain ⟨P, hP⟩ := finestLocallyConvex_submodule_closedComplemented S
  have h1 : @Continuous (FinestLocallyConvex S) S _ _ id :=
    continuous_induced_rng.2
      (continuous_of_finestLocallyConvex (E := S) (M := FinestLocallyConvex E) S.subtype)
  have h2 : @Continuous S (FinestLocallyConvex S) _ _ id := by
    have h3 := @continuous_of_finestLocallyConvex E _ _ (FinestLocallyConvex S) _ _ _ ‹_› ‹_›
      (P.toLinearMap : FinestLocallyConvex E →ₗ[ℂ] FinestLocallyConvex S)
    have : (id : S → FinestLocallyConvex S) = P ∘ Subtype.val := funext fun x ↦ (hP x).symm
    rw [this]
    exact h3.comp continuous_subtype_val
  exact le_antisymm (continuous_id_iff_le.1 (by exact h2)) (continuous_id_iff_le.1 (by exact h1))

/-- Paper: Proposition C.2.5.1(3), p. 691. The quotient topology is the finest
locally convex topology on the quotient vector space. -/
theorem finestLocallyConvex_quotient_topology (S : Submodule ℂ (FinestLocallyConvex E)) :
    (inferInstance : TopologicalSpace (FinestLocallyConvex E ⧸ S)) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex (FinestLocallyConvex E ⧸ S))) := by
  have := finestLocallyConvex_t2 E
  have := finestLocallyConvex_submodule_isClosed S
  have hT2 : T2Space (FinestLocallyConvex E ⧸ S) := inferInstance
  let _ : PolynormableSpace ℂ (FinestLocallyConvex E ⧸ S) := polynormableSpace_quotient S
  have : PolynormableSpace ℂ (FinestLocallyConvex (FinestLocallyConvex E ⧸ S)) := inferInstance
  have : T2Space (FinestLocallyConvex (FinestLocallyConvex E ⧸ S)) := finestLocallyConvex_t2 _
  have h1 : @Continuous (FinestLocallyConvex E ⧸ S) (FinestLocallyConvex (FinestLocallyConvex E ⧸ S)) _ _ id := by
    have h3 := @continuous_of_finestLocallyConvex E _ _ (FinestLocallyConvex (FinestLocallyConvex E ⧸ S)) _ _ _ ‹_› ‹_›
      ((S.mkQ : FinestLocallyConvex E →ₗ[ℂ] FinestLocallyConvex E ⧸ S) : FinestLocallyConvex E →ₗ[ℂ] FinestLocallyConvex (FinestLocallyConvex E ⧸ S))
    exact (Topology.IsQuotientMap.continuous_iff (S.isOpenQuotientMap_mkQ.isQuotientMap)).2 h3
  have h2 : @Continuous (FinestLocallyConvex (FinestLocallyConvex E ⧸ S)) (FinestLocallyConvex E ⧸ S) _ _ id :=
    @continuous_of_finestLocallyConvex (FinestLocallyConvex E ⧸ S) _ _ (FinestLocallyConvex E ⧸ S) _ _ _ ‹_› hT2 LinearMap.id
  have e1 := continuous_id_iff_le.1 h1
  have e2 := continuous_id_iff_le.1 h2
  exact le_antisymm e1 e2

open scoped NNReal

/-- In a Hamel basis, the sum of weighted absolute values of the coordinates is a seminorm. -/
private def basisWeightSeminorm {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (w : ι → ℝ≥0) : Seminorm ℂ V := by
  classical
  exact (directSumSeminorm (fun i ↦ w i • normSeminorm ℂ ℂ)).comp
    (b.repr.trans (finsuppLEquivDirectSum ℂ ℂ ι)).toLinearMap

private theorem sum_le_basisWeightSeminorm {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (w : ι → ℝ≥0) (s : Finset ι) (x : V) :
    ∑ i ∈ s, (w i : ℝ) * ‖b.repr x i‖ ≤ basisWeightSeminorm b w x := by
  classical
  exact sum_le_directSumSeminorm (fun i ↦ w i • normSeminorm ℂ ℂ)
    ((b.repr.trans (finsuppLEquivDirectSum ℂ ℂ ι)) x) s

private theorem seminorm_le_sum_basis {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (p : Seminorm ℂ V) (x : V) :
    p x ≤ ∑ i ∈ (b.repr x).support, p (b i) * ‖b.repr x i‖ := by
  have hx := b.linearCombination_repr x
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hx
  calc
    p x = p (∑ i ∈ (b.repr x).support, b.repr x i • b i) := congrArg p hx.symm
    _ ≤ _ := (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _).trans_eq
      (Finset.sum_congr rfl fun i _ ↦ by rw [map_smul_eq_mul, mul_comm])

/-- Paper: Proposition C.2.5.1(3), p. 691. The finest locally convex topology
is complete. -/
theorem finestLocallyConvex_completeSpace : CompleteSpace (FinestLocallyConvex E) := by
  classical
  let V := FinestLocallyConvex E
  let b := Module.Free.chooseBasis ℂ V
  let ι := Module.Free.ChooseBasisIndex ℂ V
  let hp := finestLocallyConvex_withSeminorms E
  refine ⟨fun {f} hf ↦ ?_⟩
  have : f.NeBot := hf.1
  let coord (i : ι) : V →L[ℂ] ℂ := ⟨b.coord i, continuous_of_finestLocallyConvex E _⟩
  choose a ha using fun i ↦ CompleteSpace.complete (hf.map (coord i).uniformContinuous)
  have hcoord (i : ι) : Tendsto (fun x : V ↦ b.repr x i) f (𝓝 (a i)) := ha i
  -- Take the coordinatewise limit in each finite weighted sum of the Cauchy differences.
  have hnear (w : ι → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ x in f, ∀ s : Finset ι, ∑ i ∈ s, (w i : ℝ) * ‖b.repr x i - a i‖ ≤ δ := by
    let p := basisWeightSeminorm b w
    have hU : {z : V × V | p (z.2 - z.1) < δ} ∈ uniformity V := by
      rw [uniformity_eq_comap_nhds_zero V]
      exact preimage_mem_comap (show {x : V | p x < δ} ∈ 𝓝 0 by
        simpa only [p.ball_zero_eq] using p.ball_mem_nhds (hp.continuous_seminorm p) hδ)
    obtain ⟨A, hA, hpair⟩ := (cauchy_iff'.mp hf).2 _ hU
    filter_upwards [hA] with x hx s
    apply le_of_tendsto (tendsto_finsetSum s fun i _ ↦
      (tendsto_const_nhds.sub (hcoord i)).norm.const_mul (w i : ℝ))
    filter_upwards [hA] with y hy
    have hxy := (sum_le_basisWeightSeminorm b w s (x - y)).trans (le_of_lt (hpair y hy x hx))
    change ∑ i ∈ s, (w i : ℝ) * ‖b.repr x i - b.repr y i‖ ≤ δ
    simpa only [map_sub, Finsupp.sub_apply] using hxy
  -- Weights reciprocal to the nonzero limiting coordinates force finite support.
  let w (i : ι) : ℝ≥0 := ‖a i‖₊⁻¹
  obtain ⟨x, hx⟩ := (hnear w (1/2) (by norm_num)).exists
  have hs : (Function.support a).Finite := (b.repr x).support.finite_toSet.subset (by
    intro i hi
    by_contra hout
    have hzero : b.repr x i = 0 := Finsupp.notMem_support_iff.mp hout
    have h := hx {i}
    have hai : a i ≠ 0 := hi
    simp [w, hzero, hai] at h
    linarith)
  let v := b.repr.symm (Finsupp.ofSupportFinite a hs)
  have hv (i : ι) : b.repr v i = a i := by simp [v]
  refine ⟨v, ?_⟩
  apply ((PolynormableSpace.hasBasis_zero_ball ℂ V).nhds_of_zero v).ge_iff.mpr
  intro p _
  let weights (i : ι) : ℝ≥0 := ⟨p (b i), apply_nonneg p _⟩
  filter_upwards [hnear weights (1/2) (by norm_num)] with y hy
  apply p.mem_ball_zero.mpr
  have h := hy (b.repr (y - v)).support
  change ∑ i ∈ (b.repr (y - v)).support, p (b i) * ‖b.repr y i - a i‖ ≤ 1/2 at h
  have hbound : p (y - v) ≤ 1/2 := (seminorm_le_sum_basis b p (y - v)).trans (by
    simpa only [map_sub, Finsupp.sub_apply, hv] using h)
  exact hbound.trans_lt (by norm_num)

/-- Paper: Proposition C.2.5.1(4), p. 692. A set is bounded for the finest
locally convex topology precisely when it lies in a finite-dimensional subspace
and is bounded in that subspace's Euclidean topology. -/
theorem finestLocallyConvex_isVonNBounded_iff (B : Set (FinestLocallyConvex E)) :
    IsVonNBounded ℂ B ↔
      ∃ S : Submodule ℂ (FinestLocallyConvex E),
        FiniteDimensional ℂ S ∧ B ⊆ S ∧ IsVonNBounded ℂ ((Subtype.val : S → _) ⁻¹' B) := by
  classical
  constructor
  · intro hB
    have hP := finestLocallyConvex_withSeminorms E
    rw [hP.isVonNBounded_iff_seminorm_bounded] at hB
    obtain ⟨A, hAB, hspan, hA⟩ := exists_linearIndependent ℂ B
    have hfinite : A.Finite := by
      by_contra hinf
      -- Assign the values 0, 1, 2, … to independent vectors of B.
      let e := (show A.Infinite from hinf).natEmbedding A
      let x : ℕ → FinestLocallyConvex E := Subtype.val ∘ e
      have hx : LinearIndependent ℂ x := hA.comp e e.injective
      let b := Module.Basis.span hx
      let f := b.constr ℂ (fun n : ℕ ↦ (n : ℂ))
      obtain ⟨g, hg⟩ := f.exists_extend
      let p : Seminorm ℂ E := (normSeminorm ℂ ℂ).comp g
      obtain ⟨r, -, hr⟩ := hB p
      obtain ⟨n, hn⟩ := exists_nat_gt r
      have hgn : g (x n) = (n : ℂ) := by
        have h := LinearMap.congr_fun hg (b n)
        simpa only [f, b, LinearMap.comp_apply, Submodule.subtype_apply,
          Module.Basis.coe_span_apply, Module.Basis.constr_basis] using h
      have hnr := hr (x n) (hAB (e n).property)
      change ‖g (x n)‖ < r at hnr
      rw [hgn, Complex.norm_natCast] at hnr
      exact lt_asymm hn hnr
    let S := Submodule.span ℂ A
    refine ⟨S, FiniteDimensional.span_of_finite ℂ hfinite, ?_, ?_⟩
    · change B ⊆ (Submodule.span ℂ A : Set _)
      rw [hspan]
      exact Submodule.subset_span
    · have hSP := S.isEmbedding_subtype.isInducing.withSeminorms hP
      rw [hSP.isVonNBounded_iff_seminorm_bounded]
      intro p
      obtain ⟨r, hr, h⟩ := hB p
      exact ⟨r, hr, fun y hy ↦ h y hy⟩
  · rintro ⟨S, -, hBS, hB⟩
    have hsub : B ⊆ S.subtypeL '' ((Subtype.val : S → _) ⁻¹' B) :=
      fun x hx ↦ ⟨⟨x, hBS hx⟩, hx, rfl⟩
    exact (hB.image S.subtypeL).subset hsub

/-- Paper: Proposition C.2.5.1(5), p. 692. A set is sequentially closed for the
finest locally convex topology precisely when each finite-dimensional section is closed. -/
theorem finestLocallyConvex_isSeqClosed_iff (C : Set (FinestLocallyConvex E)) :
    IsSeqClosed C ↔ ∀ S : Submodule ℂ (FinestLocallyConvex E), FiniteDimensional ℂ S →
      IsClosed ((Subtype.val : S → _) ⁻¹' C) := by
  have := finestLocallyConvex_t2 E
  constructor
  · intro h S hdim
    let e := (Module.finBasis ℂ S).equivFunL
    have := e.toHomeomorph.isEmbedding.metrizableSpace
    exact isSeqClosed_iff_isClosed.mp fun _ _ hu ht ↦
      h hu (continuous_subtype_val.continuousAt.tendsto.comp ht)
  · intro h f x hf ht
    obtain ⟨S, hdim, hS, -⟩ := (finestLocallyConvex_isVonNBounded_iff _).mp
      ((ht.isVonNBounded_range ℂ).insert x)
    let g (n : ℕ) : S := ⟨f n, hS (mem_insert_of_mem _ (mem_range_self n))⟩
    let y : S := ⟨x, hS (mem_insert _ _)⟩
    have hg : Tendsto g atTop (𝓝 y) := tendsto_subtype_rng.mpr ht
    exact (h S hdim).mem_of_tendsto hg (Eventually.of_forall hf)

/-- A countable Hamel basis gives an increasing exhaustion by finite-dimensional spans. -/
private theorem exists_finiteDimensional_exhaustion (hE : Module.rank ℂ E ≤ ℵ₀) :
    ∃ S : ℕ → Submodule ℂ (FinestLocallyConvex E), Monotone S ∧
      (∀ n, FiniteDimensional ℂ (S n)) ∧ ∀ x, ∃ n, x ∈ S n := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ (FinestLocallyConvex E)
  have hc := Cardinal.mk_le_aleph0_iff.mp (b.mk_eq_rank''.trans_le hE)
  let A := (countable_range b).finiteExhaustion
  let S (n : ℕ) := Submodule.span ℂ (A n)
  have hmono : Monotone S := fun _ _ h ↦ Submodule.span_mono (A.mono h)
  refine ⟨S, hmono, fun n ↦ FiniteDimensional.span_of_finite ℂ (A.finite n), fun x ↦ ?_⟩
  apply (Submodule.mem_iSup_of_directed S hmono.directed_le).mp
  have htop : (⨆ n, S n) = ⊤ := by
    change (⨆ n, Submodule.span ℂ (A n)) = ⊤
    rw [Submodule.iSup_span, A.iUnion_eq, b.span_eq]
  simp [htop]

/-- Any family of subspaces of the finest space tests continuity of every seminorm. -/
private theorem finestLocallyConvex_finalTopology (S : ℕ → Submodule ℂ (FinestLocallyConvex E)) :
    (inferInstance : TopologicalSpace (FinestLocallyConvex E)) =
      locallyConvexFinalTopology (fun n ↦ (S n).subtype) := by
  let hp := finestLocallyConvex_withSeminorms E
  let e : {p : Seminorm ℂ E // ∀ n, Continuous (p ∘ (S n).subtype)} ≃ Seminorm ℂ E :=
    Equiv.subtypeUnivEquiv fun p n ↦ (hp.continuous_seminorm p).comp continuous_subtype_val
  exact (hp.congr_equiv e).topology_eq_withSeminorms

/-- Paper: Proposition C.2.5.1(6), p. 692. With its finest locally convex topology,
a countably generated vector space is a strict LF-space. -/
theorem finestLocallyConvex_isStrictLFSpace (hE : Module.rank ℂ E ≤ ℵ₀) :
    IsStrictLFSpace (FinestLocallyConvex E) := by
  obtain ⟨S, hS, hdim, hcover⟩ := exists_finiteDimensional_exhaustion hE
  refine ⟨finestLocallyConvex_t2 E, S, hS, fun n ↦ ?_, hcover,
    finestLocallyConvex_finalTopology S⟩
  have := finestLocallyConvex_t2 E
  let e := (Module.finBasis ℂ (S n)).equivFunL
  exact ⟨inferInstance, inferInstance, e.toHomeomorph.isEmbedding.metrizableSpace, by
    let : UniformSpace (S n) := IsTopologicalAddGroup.rightUniformSpace (S n)
    let : IsUniformAddGroup (S n) := isUniformAddGroup_of_addCommGroup
    exact FiniteDimensional.completeSpace ℂ (S n)⟩

/-- The local integral criterion is independent of the universe of test spaces. -/
theorem nuclear_changeUniverse.{a, b, c} {X : Type c} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (hX : IsNuclearTVS.{a} X) : IsNuclearTVS.{b} X := by
  let := hX.1
  let := hX.2.1
  exact (isNuclearTVS_iff_localBanach_integral X).mpr
    ((isNuclearTVS_iff_localBanach_integral X).mp hX)

/-- Nuclearity is invariant under continuous linear equivalence, across carrier universes. -/
theorem nuclear_of_equiv {X : Type u} {Y : Type w}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    (e : X ≃L[ℂ] Y) (hX : IsNuclearTVS.{v} X) : IsNuclearTVS.{v} Y := by
  let := hX.1
  let := hX.2.1
  have : T2Space Y := e.toHomeomorph.t2Space
  have h := nuclear_changeUniverse.{v, max v w} hX
  apply nuclear_changeUniverse.{max v u, v}
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro F _ _ _ _ _
  let eX := (h.2.2 F inferInstance inferInstance inferInstance inferInstance inferInstance).homeomorph
  have hback : Continuous (show InjectiveTensor X F → ProjectiveTensor X F from id) :=
    eX.continuous_symm.congr fun z ↦ eX.apply_symm_apply z
  let idF := ContinuousLinearMap.id ℂ F
  have he : Continuous (show InjectiveTensor Y F → ProjectiveTensor Y F from id) := by
    refine ((projectiveTensorMap_continuous e.toContinuousLinearMap idF).comp hback |>.comp
      (injectiveTensorMap_continuous e.symm.toContinuousLinearMap idF)).congr fun z ↦ ?_
    change Y ⊗[ℂ] F at z
    change e.toLinearMap.rTensor F (e.symm.toLinearMap.rTensor F z) = z
    rw [← LinearMap.rTensor_comp_apply, show e.toLinearMap.comp e.symm.toLinearMap =
      LinearMap.id from LinearMap.ext e.apply_symm_apply, LinearMap.rTensor_id_apply]
  exact (⟨Equiv.refl (Y ⊗[ℂ] F), (uniformContinuous_tensorComparison Y F).continuous, he⟩ :
    ProjectiveTensor Y F ≃ₜ InjectiveTensor Y F).isHomeomorph

/-- A Hausdorff injective limit is a Hausdorff quotient of the direct sum of its stages. -/
private theorem nuclear_of_injectiveLCLimit {D : Type*} [AddCommGroup D] [Module ℂ D]
    [TopologicalSpace D] [T2Space D] {X : ℕ → Type*}
    [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)] [∀ k, TopologicalSpace (X k)]
    {j : ∀ k, X k →L[ℂ] X (k+1)} {i : ∀ k, X k →L[ℂ] D} (h : IsInjectiveLCLimit j i)
    (hX : ∀ k, IsNuclearTVS.{v} (X k)) : IsNuclearTVS.{v} D := by
  let P := ⨁ k, X k
  let : TopologicalSpace P := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
  have hP : IsNuclearTVS.{v} P := isNuclearTVS_directSum hX
  let := hP.2.1
  let := PolynormableSpace.isTopologicalAddGroup ℂ P
  let hD : WithSeminorms (Subtype.val :
      {p : Seminorm ℂ D // ∀ k, Continuous (p ∘ i k)} → Seminorm ℂ D) := ⟨h.topology_eq⟩
  let := hD.toPolynormableSpace
  let := hD.isTopologicalAddGroup
  let : ∀ k, PolynormableSpace ℂ (X k) := fun k ↦ (hX k).2.1
  let : ∀ k, IsTopologicalAddGroup (X k) := fun k ↦ PolynormableSpace.isTopologicalAddGroup ℂ _
  let q : P →ₗ[ℂ] D := DirectSum.toModule ℂ ℕ D fun k ↦ (i k).toLinearMap
  have hq : IsQuotientMap q := h.isQuotientMap_directSum
  let e := q.quotKerEquivOfSurjective hq.surjective
  have he : Continuous e := q.ker.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr hq.continuous
  have hi : Continuous e.symm := hq.continuous_iff.mpr (by
    exact q.ker.isOpenQuotientMap_mkQ.continuous.congr fun x ↦
      (q.quotKerEquivOfSurjective_symm_apply hq.surjective x).symm)
  let L : (P ⧸ q.ker) ≃L[ℂ] D := ⟨e, he, hi⟩
  let := L.symm.toHomeomorph.t2Space
  exact nuclear_of_equiv L (isNuclearTVS_quotient hP q.ker)

/-- Increasing nuclear subspaces with the final locally convex topology have nuclear union. -/
private theorem nuclear_of_submodule_exhaustion {D : Type*} [AddCommGroup D] [Module ℂ D]
    [TopologicalSpace D] [T2Space D] (S : ℕ → Submodule ℂ D) (hS : Monotone S)
    (hn : ∀ n, IsNuclearTVS.{v} (S n)) (hex : ∀ x, ∃ n, x ∈ S n)
    (ht : (inferInstance : TopologicalSpace D) = locallyConvexFinalTopology (fun k ↦ (S k).subtype)) :
    IsNuclearTVS.{v} D := by
  let j (k : ℕ) := (S k).subtypeL.codRestrict (S (k+1)) fun x ↦ hS k.le_succ x.property
  have h : IsInjectiveLCLimit j (fun k ↦ (S k).subtypeL) := by
    refine ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ ?_, ht⟩
    obtain ⟨k, hk⟩ := hex x
    exact ⟨k, ⟨⟨x, hk⟩, rfl⟩⟩
  exact nuclear_of_injectiveLCLimit h hn

/-- Paper: Proposition C.2.5.1(6), p. 692. With its finest locally convex topology,
a countably generated vector space is nuclear. -/
theorem finestLocallyConvex_isNuclearTVS (hE : Module.rank ℂ E ≤ ℵ₀) :
    IsNuclearTVS.{v, u} (FinestLocallyConvex E) := by
  have := finestLocallyConvex_t2 E
  obtain ⟨S, hS, hdim, hcover⟩ := exists_finiteDimensional_exhaustion hE
  exact nuclear_of_submodule_exhaustion S hS (fun n ↦ isNuclearTVS_of_finiteDimensional (S n))
    hcover (finestLocallyConvex_finalTopology S)

/-- Paper: Proposition C.2.5.1(6), p. 692. In countable dimension the finest locally
convex topology has the Heine–Borel property. -/
theorem finestLocallyConvex_montelSpace (hE : Module.rank ℂ E ≤ ℵ₀) :
    MontelSpace ℂ (FinestLocallyConvex E) := by
  have := finestLocallyConvex_t2 E
  refine ⟨fun B hclosed hb ↦ ?_⟩
  obtain ⟨S, hdim, hBS, hbS⟩ := (finestLocallyConvex_isVonNBounded_iff B).mp hb
  let e := (Module.finBasis ℂ S).equivFunL
  let A := (Subtype.val : S → _) ⁻¹' B
  have hc := e.toHomeomorph.isClosedMap A (hclosed.preimage continuous_subtype_val)
  have hb' := hbS.image e.toContinuousLinearMap
  have hk := Metric.isCompact_of_isClosed_isBounded hc ((NormedSpace.isVonNBounded_iff ℂ).mp hb')
  have hA : IsCompact A := e.toHomeomorph.isEmbedding.isCompact_iff.mpr hk
  simpa only [A, image_preimage_eq_of_subset (by simpa using hBS : B ⊆ range (Subtype.val : S → _))]
    using hA.image continuous_subtype_val

/-- Paper: Proposition C.2.5.1(6), p. 692. In countable dimension the evaluation
map from the finest locally convex space onto its strong bidual is a homeomorphism.
Together with the Heine–Borel property this states the paper's Montel conclusion. -/
theorem finestLocallyConvex_strongBidual (hE : Module.rank ℂ E ≤ ℵ₀) :
    IsHomeomorph (ContinuousLinearMap.applyₗ (E := FinestLocallyConvex E) ℂ (RingHom.id ℂ)) := by
  have := finestLocallyConvex_t2 E
  have := finestLocallyConvex_montelSpace hE
  have : BarrelledSpace ℂ (FinestLocallyConvex E) :=
    ⟨fun p _ ↦ (finestLocallyConvex_withSeminorms E).continuous_seminorm p⟩
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨isEmbedding_strongBidual_eval, surjective_strongBidual_eval⟩

/-- Evaluation on a Hamel basis identifies the strong dual of the finest space with
the product of copies of the scalar field indexed by the basis. -/
private def finestStrongDualEquiv (E : Type u) [AddCommGroup E] [Module ℂ E] :
    StrongDual ℂ (FinestLocallyConvex E) ≃L[ℂ]
      (Module.Free.ChooseBasisIndex ℂ (FinestLocallyConvex E) → ℂ) := by
  classical
  let W := FinestLocallyConvex E
  let D := StrongDual ℂ W
  let ι := Module.Free.ChooseBasisIndex ℂ W
  let b : Module.Basis ι ℂ W := Module.Free.chooseBasis ℂ W
  let : T2Space W := finestLocallyConvex_t2 E
  let : ContinuousSMul ℂ W := (finestLocallyConvex_withSeminorms E).continuousSMul
  let e : D ≃ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun f i ↦ f (b i)
      invFun := fun z ↦ ⟨b.constr ℂ z, continuous_of_finestLocallyConvex E _⟩
      left_inv := fun f ↦ ContinuousLinearMap.ext fun x ↦ LinearMap.congr_fun
        (b.constr_eq ℂ (f := f.toLinearMap) fun _ ↦ rfl) x
      right_inv := fun z ↦ funext (b.constr_basis ℂ z)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hEval : Continuous e := continuous_pi fun i ↦ continuous_eval_const (b i)
  have hContValue (x : W) : Continuous (fun z : ι → ℂ ↦ e.symm z x) := by
    change Continuous (fun z : ι → ℂ ↦ (b.constr ℂ z) x)
    simp only [b.constr_apply, Finsupp.sum]
    exact continuous_finsetSum _ fun i _ ↦
      (continuous_apply i : Continuous (fun z : ι → ℂ ↦ z i)).const_smul (b.repr x i)
  -- On a bounded set, uniform convergence is controlled by finitely many evaluations.
  have hInv : Continuous e.symm := by
    apply continuous_of_tendsto_nhds_zero e.symm
    apply ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff.mpr
    rintro ⟨B, U⟩ ⟨hB, hU⟩
    obtain ⟨S, hdim, hBS, hbounded⟩ := (finestLocallyConvex_isVonNBounded_iff B).mp hB
    -- Restrict to S by recording the evaluations on its basis.
    let c := Module.finBasis ℂ S
    let restrictBasis := (c.constr ℂ).trans
      (LinearMap.toContinuousLinearMap : (S →ₗ[ℂ] ℂ) ≃ₗ[ℂ] StrongDual ℂ S)
    let r (z : ι → ℂ) : StrongDual ℂ S := restrictBasis (fun i ↦ e.symm z (c i : W))
    have hr : Continuous r := restrictBasis.toLinearMap.continuous_of_finiteDimensional.comp
      (continuous_pi fun i ↦ hContValue (c i : W))
    have hr_zero : r 0 = 0 := by simp [r]; rfl
    have ht : Tendsto r (𝓝 0) (𝓝 0) := hr_zero ▸ hr.continuousAt
    filter_upwards [ht.eventually (ContinuousLinearMap.eventually_nhds_zero_mapsTo hbounded hU)]
      with z hz
    intro x hx
    let y : S := ⟨x, hBS hx⟩
    have hy : r z y = e.symm z x := by
      have heq : (r z).toLinearMap = (e.symm z).toLinearMap.comp S.subtype := by
        apply c.ext
        intro i
        exact c.constr_basis ℂ (fun i ↦ e.symm z (c i : W)) i
      exact LinearMap.congr_fun heq y
    exact hy ▸ hz (show y ∈ Subtype.val ⁻¹' B from hx)
  exact ⟨e, hEval, hInv⟩

/-- Paper: Proposition C.2.5.1(6), p. 692. The strong dual of a countably generated
space with the finest locally convex topology is Fréchet. -/
theorem finestLocallyConvex_strongDual_isFrechetTVS (hE : Module.rank ℂ E ≤ ℵ₀) :
    IsFrechetTVS (StrongDual ℂ (FinestLocallyConvex E)) := by
  let D := StrongDual ℂ (FinestLocallyConvex E)
  let dualEquiv := finestStrongDualEquiv E
  have := Cardinal.mk_le_aleph0_iff.mp
    ((Module.Free.chooseBasis ℂ (FinestLocallyConvex E)).mk_eq_rank''.trans_le hE)
  have hInd := dualEquiv.toHomeomorph.isInducing
  refine ⟨inferInstance, dualEquiv.PolynormableSpace,
    dualEquiv.toHomeomorph.isEmbedding.metrizableSpace, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq (G := D)]
  exact (AddMonoidHom.isUniformInducing_of_isInducing (f := dualEquiv.toLinearEquiv.toAddMonoidHom)
    hInd).completeSpace_congr dualEquiv.surjective |>.mpr inferInstance

-- TODO(paper-gap): In the proof of C.2.5.1(6), an infinite-dimensional countably
-- generated space with the finest locally convex topology need not be Fréchet.

/-- Paper: Proposition C.2.5.1(6), p. 692. The strong dual of a countably generated
space with the finest locally convex topology is nuclear. -/
theorem finestLocallyConvex_strongDual_isNuclearTVS (hE : Module.rank ℂ E ≤ ℵ₀) :
    IsNuclearTVS.{v, u} (StrongDual ℂ (FinestLocallyConvex E)) := by
  let e := finestStrongDualEquiv E
  let := e.PolynormableSpace
  exact nuclear_of_equiv e.symm
    (isNuclearTVS_pi (X := fun _ ↦ ℂ) (fun _ ↦ isNuclearTVS_of_finiteDimensional ℂ))

variable {F : Type*} [AddCommGroup F] [Module ℂ F]

/-- A nonnegative matrix on two countable index sets is bounded by a product
of weights. Split the matrix into the two triangles given by numberings. -/
private theorem exists_product_weights {I J : Type*} [Countable I] [Countable J]
    (m : I → J → ℝ≥0) : ∃ w : I → ℝ≥0, ∃ v : J → ℝ≥0, ∀ i j, m i j ≤ w i * v j := by
  classical
  obtain ⟨a, ha⟩ := exists_injective_nat I
  obtain ⟨b, hb⟩ := exists_injective_nat J
  let A (n : ℕ) := ((finite_Iic n).preimage ha.injOn).toFinset
  let B (n : ℕ) := ((finite_Iic n).preimage hb.injOn).toFinset
  let w i := max 1 ((B (a i)).sup (m i))
  let v j := max 1 ((A (b j)).sup (fun i ↦ m i j))
  refine ⟨w, v, fun i j ↦ ?_⟩
  rcases le_total (b j) (a i) with h | h
  · have hj : j ∈ B (a i) := by simpa [B] using h
    exact ((Finset.le_sup hj).trans (le_max_right _ _)).trans
      (le_mul_of_one_le_right (show 0 ≤ w i from zero_le) (le_max_left 1 _))
  · have hi : i ∈ A (b j) := by simpa [A] using h
    exact ((Finset.le_sup hi).trans (le_max_right _ _)).trans
      (le_mul_of_one_le_left (show 0 ≤ v j from zero_le) (le_max_left 1 _))

/-- Paper: Lemma C.2.5.2, p. 692. The projective tensor topology of two countably
generated spaces with the finest locally convex topologies is again the finest
locally convex topology, which is complete by Proposition C.2.5.1(3). -/
theorem finestLocallyConvex_projectiveTensor (hE : Module.rank ℂ E ≤ ℵ₀)
    (hF : Module.rank ℂ F ≤ ℵ₀) :
    (inferInstance : TopologicalSpace (ProjectiveTensor (FinestLocallyConvex E) (FinestLocallyConvex F))) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex (E ⊗[ℂ] F))) := by
  classical
  let X := FinestLocallyConvex E
  let Y := FinestLocallyConvex F
  let b := Module.Free.chooseBasis ℂ X
  let c := Module.Free.chooseBasis ℂ Y
  have := Cardinal.mk_le_aleph0_iff.mp (b.mk_eq_rank''.trans_le hE)
  have := Cardinal.mk_le_aleph0_iff.mp (c.mk_eq_rank''.trans_le hF)
  let hP := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
      ContinuousAt (fun z : X × Y ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0} ↦ p.val)
  let hf := finestLocallyConvex_withSeminorms (E ⊗[ℂ] F)
  suffices h : ∀ p : Seminorm ℂ (E ⊗[ℂ] F), ContinuousAt (fun z : X × Y ↦ p (z.1 ⊗ₜ[ℂ] z.2)) 0 by
    let e := Equiv.subtypeUnivEquiv h
    exact hP.topology_eq_withSeminorms.trans (hf.congr_equiv e).topology_eq_withSeminorms.symm
  intro r
  obtain ⟨w, v, hwv⟩ := exists_product_weights (fun i j ↦
    (⟨r (b i ⊗ₜ[ℂ] c j), apply_nonneg r _⟩ : ℝ≥0))
  let p := basisWeightSeminorm b w
  let q := basisWeightSeminorm c v
  have hrow (i) (y : Y) : r (b i ⊗ₜ[ℂ] y) ≤ w i * q y := by
    let s := (c.repr y).support
    calc
      _ ≤ ∑ j ∈ s, r (b i ⊗ₜ[ℂ] c j) * ‖c.repr y j‖ :=
        seminorm_le_sum_basis c (r.comp (TensorProduct.mk ℂ X Y (b i))) y
      _ ≤ ∑ j ∈ s, (w i : ℝ) * ((v j : ℝ) * ‖c.repr y j‖) := by
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (show r (b i ⊗ₜ[ℂ] c j) ≤ w i * v j from hwv i j)
          (norm_nonneg _)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_le_basisWeightSeminorm c v s y) (w i).coe_nonneg
  have hbound (x : X) (y : Y) : r (x ⊗ₜ[ℂ] y) ≤ p x * q y := by
    let s := (b.repr x).support
    calc
      _ ≤ ∑ i ∈ s, r (b i ⊗ₜ[ℂ] y) * ‖b.repr x i‖ :=
        seminorm_le_sum_basis b (r.comp ((TensorProduct.mk ℂ X Y).flip y)) x
      _ ≤ ∑ i ∈ s, ((w i : ℝ) * ‖b.repr x i‖) * q y := by
        apply Finset.sum_le_sum
        intro i _
        rw [mul_right_comm]
        exact mul_le_mul_of_nonneg_right (hrow i y) (norm_nonneg _)
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (sum_le_basisWeightSeminorm b w s x) (apply_nonneg q _)
  have hp := ((finestLocallyConvex_withSeminorms E).continuous_seminorm p).comp
    (continuous_fst : Continuous (Prod.fst : X × Y → X))
  have hq := ((finestLocallyConvex_withSeminorms F).continuous_seminorm q).comp
    (continuous_snd : Continuous (Prod.snd : X × Y → Y))
  have hzero : r ((0 : X × Y).1 ⊗ₜ[ℂ] (0 : X × Y).2) = 0 := by
    change r ((0 : E) ⊗ₜ[ℂ] (0 : F)) = 0
    simp
  rw [ContinuousAt, hzero]
  refine squeeze_zero (fun z : X × Y ↦ apply_nonneg r (z.1 ⊗ₜ[ℂ] z.2)) (fun z ↦ hbound z.1 z.2) ?_
  have hc : Continuous (fun z : X × Y ↦ p z.1 * q z.2) := hp.mul hq
  have ht := hc.tendsto (0 : X × Y)
  change Tendsto _ _ (𝓝 (p 0 * q 0)) at ht
  simpa only [map_zero, zero_mul] using ht

/-- Paper: Lemma C.2.5.2, p. 692. The injective tensor topology of two countably
generated spaces with the finest locally convex topologies is again the finest
locally convex topology, which is complete by Proposition C.2.5.1(3). -/
theorem finestLocallyConvex_injectiveTensor (hE : Module.rank ℂ E ≤ ℵ₀)
    (hF : Module.rank ℂ F ≤ ℵ₀) :
    (inferInstance : TopologicalSpace (InjectiveTensor (FinestLocallyConvex E) (FinestLocallyConvex F))) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex (E ⊗[ℂ] F))) := by
  have := finestLocallyConvex_t2 E
  have hN := finestLocallyConvex_isNuclearTVS.{0} hE
  have hback := continuous_injectiveTensor_to_projectiveTensor_of_localSeries
    (FinestLocallyConvex E) ((isNuclearTVS_iff_localBanach_series _).mp hN)
    (FinestLocallyConvex F)
  exact (le_antisymm (continuous_id_iff_le.mp hback)
    (continuous_id_iff_le.mp (uniformContinuous_tensorComparison (FinestLocallyConvex E)
      (FinestLocallyConvex F)).continuous)).trans (finestLocallyConvex_projectiveTensor hE hF)

/-- Paper: Lemma C.2.5.2, p. 692. The inductive tensor topology of two countably
generated spaces with the finest locally convex topologies is again the finest
locally convex topology, which is complete by Proposition C.2.5.1(3). -/
theorem finestLocallyConvex_inductiveTensor (hE : Module.rank ℂ E ≤ ℵ₀)
    (hF : Module.rank ℂ F ≤ ℵ₀) :
    (inferInstance : TopologicalSpace (InductiveTensor (FinestLocallyConvex E) (FinestLocallyConvex F))) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex (E ⊗[ℂ] F))) := by
  have hsp := withGeneratingSeminorms_spec (E ⊗[ℂ] F)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] F) //
      (∀ x : FinestLocallyConvex E, Continuous (fun y : FinestLocallyConvex F ↦ p (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : FinestLocallyConvex F, Continuous (fun x : FinestLocallyConvex E ↦ p (x ⊗ₜ[ℂ] y)))} ↦
        p.val)
  have hfin := finestLocallyConvex_withSeminorms (E ⊗[ℂ] F)
  have := hsp.isTopologicalAddGroup
  have := hfin.isTopologicalAddGroup
  have h1 : @Continuous (FinestLocallyConvex (E ⊗[ℂ] F))
      (InductiveTensor (FinestLocallyConvex E) (FinestLocallyConvex F)) _ _ id :=
    hsp.continuous_of_continuous_comp (LinearMap.id : FinestLocallyConvex (E ⊗[ℂ] F) →ₗ[ℂ] _)
      fun p ↦ hfin.continuous_seminorm p.val
  have h2 : @Continuous (InductiveTensor (FinestLocallyConvex E) (FinestLocallyConvex F))
      (FinestLocallyConvex (E ⊗[ℂ] F)) _ _ id := by
    refine hfin.continuous_of_continuous_comp
      (LinearMap.id : InductiveTensor (FinestLocallyConvex E) (FinestLocallyConvex F) →ₗ[ℂ] _)
      fun q ↦ hsp.continuous_seminorm ⟨q, fun x ↦ ?_, fun y ↦ ?_⟩
    · exact (finestLocallyConvex_withSeminorms F).continuous_seminorm
        (q.comp (TensorProduct.mk ℂ E F x))
    · exact (finestLocallyConvex_withSeminorms E).continuous_seminorm
        (q.comp ((TensorProduct.mk ℂ E F).flip y))
  exact le_antisymm (continuous_id_iff_le.1 h2) (continuous_id_iff_le.1 h1)

end FinestLocallyConvex

/-! ## Deferred from §C.1 -/

section Deferred

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Paper: Remark C.1.4.7, p. 663. A strict countable inductive limit of nuclear
Fréchet spaces is nuclear.
Deviation: The stages are represented by their increasing images in the limit. -/
theorem isNuclearTVS_of_strictLF_stages [T2Space E]
    (S : ℕ → Submodule ℂ E) (hS : Monotone S)
    (hFrechet : ∀ n, IsFrechetTVS (S n)) (hNuclear : ∀ n, IsNuclearTVS.{v} (S n))
    (hexhaustive : ∀ x : E, ∃ n, x ∈ S n)
    (ht : (inferInstance : TopologicalSpace E) = locallyConvexFinalTopology (fun n ↦ (S n).subtype)) :
    IsNuclearTVS.{v} E := by
  exact nuclear_of_submodule_exhaustion S hS hNuclear hexhaustive ht

/-- Paper: Remark C.1.4.7, p. 663. A nuclear strict LF-space has the Heine–Borel
property. Each stage in a strict presentation is nuclear by Remark C.1.5.12. -/
theorem montelSpace_of_nuclear_strictLF (hLF : IsStrictLFSpace E) (hE : IsNuclearTVS.{v} E) :
    MontelSpace ℂ E := by
  let := hE.1
  let := hE.2.1
  let := PolynormableSpace.isTopologicalAddGroup ℂ E
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let := hLF.completeSpace
  refine ⟨fun B hc hb ↦ ?_⟩
  simpa only [hc.closure_eq] using isCompact_closure_of_isNuclearTVS E hE hb

/-- Paper: Remark C.1.4.7, p. 663. Evaluation from a nuclear strict LF-space to
the strong bidual is a homeomorphism. Along with the Heine–Borel property, this
states the paper's Montel conclusion. -/
theorem strongBidual_of_nuclear_strictLF [ContinuousSMul ℂ E]
    (hLF : IsStrictLFSpace E) (hE : IsNuclearTVS.{v} E) :
    IsHomeomorph (ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ)) := by
  let := hE.1
  let := hE.2.1
  let := PolynormableSpace.isTopologicalAddGroup ℂ E
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let := montelSpace_of_nuclear_strictLF hLF hE
  obtain ⟨_, S, _, hF, _, ht⟩ := hLF
  have hP : WithSeminorms (Subtype.val :
      {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ (S k).subtype)} → Seminorm ℂ E) := ⟨ht⟩
  have : BarrelledSpace ℂ E := by
    refine ⟨fun p hp ↦ hP.continuous_seminorm ⟨p, fun k ↦ ?_⟩⟩
    have := isFrechetTVS_barrelled (hF k)
    exact (p.comp (S k).subtype).continuous_of_lowerSemicontinuous (hp.comp continuous_subtype_val)
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨isEmbedding_strongBidual_eval, surjective_strongBidual_eval⟩

/-- Paper: Example C.1.5.10, p. 668. A nuclear locally convex space is Schwartz. -/
theorem isSchwartzTVS_of_isNuclearTVS (hE : IsNuclearTVS.{v} E) : IsSchwartzTVS E := by
  let := hE.1
  let := hE.2.1
  let := PolynormableSpace.isTopologicalAddGroup ℂ E
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  refine ⟨inferInstance, fun q hq ↦ ?_⟩
  obtain ⟨K, hK, hV⟩ := isCompactOperator_localBanach_coe E hE q hq
  refine ⟨_, hV, ?_⟩
  change TotallyBounded (((↑) : WithLocalSeminorm q → LocalBanach q) ⁻¹' K)
  exact totallyBounded_preimage (Completion.isUniformInducing_coe (WithLocalSeminorm q))
    hK.totallyBounded

variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
  [∀ n, TopologicalSpace (X n)] {j : ∀ n, X n →L[ℂ] X (n + 1)} {i : ∀ n, X n →L[ℂ] E}

/-- Paper: Theorem C.1.5.11, p. 668. In a strict countable limit of nuclear Fréchet
spaces a closed subspace is a limit subspace exactly when its quotient map lifts bounded sets. -/
theorem isLimitSubspace_iff_liftsBoundedSets_of_nuclear
    (h : IsInjectiveLCLimit j i) (hj : ∀ n, IsEmbedding (j n))
    (hFrechet : ∀ n, IsFrechetTVS (X n)) (hNuclear : ∀ n, IsNuclearTVS.{v} (X n))
    (F : Submodule ℂ E) (hF : IsClosed (F : Set E)) :
    IsLimitSubspace i F ↔ LiftsBoundedSets F.mkQL := by
  exact (and_iff_right hF).trans (limitSubspaceTopology_eq_iff_liftsBoundedSets hFrechet
    (fun k ↦ isSchwartzTVS_of_isNuclearTVS (hNuclear k)) h hj F
    (fun k ↦ hF.preimage (i k).continuous))

-- TODO(paper-gap): The paragraph after Theorem C.1.5.11 reverses the implication
-- of Example C.1.5.10. Nuclear spaces are Schwartz.

/-- Paper: Remark C.1.5.12, p. 668. Every strict defining sequence of a nuclear
strict LF-space has nuclear stages. By Remark C.1.4.7 nuclearity of the limit follows
from any one strict presentation by nuclear Fréchet stages. -/
theorem isNuclearTVS_strictLF_stage
    (h : IsInjectiveLCLimit j i) (hj : ∀ n, IsEmbedding (j n))
    (hFrechet : ∀ n, IsFrechetTVS (X n)) (hE : IsNuclearTVS.{v} E) (n : ℕ) :
    IsNuclearTVS.{v} (X n) := by
  let : ∀ k, PolynormableSpace ℂ (X k) := fun k ↦ (hFrechet k).choose_spec.1
  let : ∀ k, IsTopologicalAddGroup (X k) := fun k ↦ (hFrechet k).choose
  have hi := h.isEmbedding_stage hj n
  let e := LinearEquiv.ofInjective (i n).toLinearMap hi.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hi.isInducing
  let t := e.toEquiv.toHomeomorphOfIsInducing he
  let L : X n ≃L[ℂ] (i n).toLinearMap.range := ⟨e, t.continuous, t.continuous_symm⟩
  exact nuclear_of_equiv L.symm (isNuclearTVS_submodule hE (i n).toLinearMap.range)

/-- In a strict LF presentation by subspaces a bounded set is the image of a bounded
set in one of the given Fréchet stages. -/
private theorem exists_bounded_stage_of_exhaustion {D : Type*} [AddCommGroup D] [Module ℂ D]
    [TopologicalSpace D] (S : ℕ → Submodule ℂ D) (hS : Monotone S)
    (hF : ∀ n, IsFrechetTVS (S n)) (hex : ∀ x, ∃ n, x ∈ S n)
    (ht : (inferInstance : TopologicalSpace D) = locallyConvexFinalTopology (fun k ↦ (S k).subtype))
    {B : Set D} (hb : IsVonNBounded ℂ B) :
    ∃ k, ∃ A : Set (S k), IsVonNBounded ℂ A ∧ (S k).subtypeL '' A = B := by
  choose hadd hpoly hmet hcomplete using hF
  let := hadd
  let := hpoly
  let := hmet
  let : ∀ k, UniformSpace (S k) := fun k ↦ IsTopologicalAddGroup.rightUniformSpace (S k)
  let : ∀ k, IsUniformAddGroup (S k) := fun _ ↦ isUniformAddGroup_of_addCommGroup
  let : ∀ k, CompleteSpace (S k) := hcomplete
  let j (k : ℕ) := (S k).subtypeL.codRestrict (S (k+1)) fun x ↦ hS k.le_succ x.property
  have h : IsInjectiveLCLimit j (fun k ↦ (S k).subtypeL) := by
    refine ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ ?_, ht⟩
    obtain ⟨k, hk⟩ := hex x
    exact ⟨k, ⟨⟨x, hk⟩, rfl⟩⟩
  have hj (k : ℕ) : IsEmbedding (j k) :=
    IsEmbedding.of_comp (j k).continuous continuous_subtype_val IsEmbedding.subtypeVal
  exact (isVonNBounded_iff_bounded_stage h (fun k ↦
    (AddMonoidHom.isUniformEmbedding_of_isEmbedding (hj k)).isClosedEmbedding) B).mp hb

/-- If a closed limit subspace has the final topology of its intersections with the
stages, the images of these Fréchet intersections give a strict LF presentation. -/
private theorem strictLFSpace_of_limitSubspace
    (h : IsInjectiveLCLimit j i) (hj : ∀ n, IsEmbedding (j n))
    (hFrechet : ∀ n, IsFrechetTVS (X n)) (F : Submodule ℂ E) (hF : IsLimitSubspace i F) :
    IsStrictLFSpace F := by
  choose hadd hpoly hmet hcomplete using hFrechet
  let := hadd
  let := hpoly
  let := hmet
  let : ∀ k, UniformSpace (X k) := fun k ↦ IsTopologicalAddGroup.rightUniformSpace (X k)
  let : ∀ k, IsUniformAddGroup (X k) := fun _ ↦ isUniformAddGroup_of_addCommGroup
  let : ∀ k, CompleteSpace (X k) := hcomplete
  let K (k : ℕ) := F.comap (i k).toLinearMap
  let l (k : ℕ) : K k →ₗ[ℂ] F := (i k).toLinearMap.restrict (fun _ hx ↦ hx)
  have hl (k : ℕ) : IsEmbedding (l k) :=
    IsEmbedding.subtypeVal.of_comp_iff.mp ((h.isEmbedding_stage hj k).comp IsEmbedding.subtypeVal)
  let S (k : ℕ) := (l k).range
  let e (k : ℕ) := LinearEquiv.ofInjective (l k) (hl k).injective
  have he (k : ℕ) : IsInducing (e k) := IsInducing.subtypeVal.of_comp_iff.mp (hl k).isInducing
  let t k := (e k).toEquiv.toHomeomorphOfIsInducing (he k)
  have hc (k : ℕ) : IsClosed (K k : Set (X k)) := hF.1.preimage (i k).continuous
  refine ⟨inferInstance, S, monotone_nat_of_le_succ (fun k ↦ ?_), fun k ↦ ?_, fun x ↦ ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    have heq := DFunLike.congr_fun (h.compatible k) x.val
    exact ⟨⟨j k x, show i (k+1) (j k x) ∈ F from heq.symm ▸ x.property⟩, Subtype.ext heq⟩
  · have : TopologicalSpace.MetrizableSpace (X k) := hmet k
    have : TopologicalSpace.MetrizableSpace (K k) := (K k).isEmbedding_subtype.metrizableSpace
    let L : K k ≃L[ℂ] S k := ⟨e k, (t k).continuous, (t k).continuous_symm⟩
    let : IsUniformAddGroup (K k) := IsUniformAddGroup.comap (f := (K k).subtype.toAddMonoidHom)
    let : CompleteSpace (K k) := (hc k).completeSpace_coe
    refine ⟨inferInstance, L.symm.PolynormableSpace, L.symm.toHomeomorph.isEmbedding.metrizableSpace, ?_⟩
    let : UniformSpace (S k) := IsTopologicalAddGroup.rightUniformSpace (S k)
    let : IsUniformAddGroup (S k) := isUniformAddGroup_of_addCommGroup
    exact ((AddMonoidHom.isUniformInducing_of_isInducing (f := L.toLinearEquiv.toAddMonoidHom)
      (he k)).completeSpace_congr L.surjective).mp inferInstance
  · obtain ⟨k, y, hy⟩ := h.exhaustive x.val
    exact ⟨k, ⟨⟨y, show i k y ∈ F from hy.symm ▸ x.property⟩, Subtype.ext hy⟩⟩
  · have heq : (fun p : Seminorm ℂ F ↦ ∀ k, Continuous (p ∘ l k)) =
        (fun p : Seminorm ℂ F ↦ ∀ k, Continuous (p ∘ (S k).subtype)) := by
      funext p
      apply propext
      exact ⟨fun hp k ↦ ((t k).isQuotientMap.continuous_iff).mpr (hp k),
        fun hp k ↦ (hp k).comp (t k).continuous⟩
    refine hF.2.trans ?_
    change (SeminormFamily.moduleFilterBasis
      (Subtype.val : {p : Seminorm ℂ F // ∀ k, Continuous (p ∘ l k)} → _)).topology = _
    rw [heq]
    rfl

/-- Paper: Corollary C.1.5.13, p. 668. If a strict countable limit of nuclear
Fréchet spaces has a quotient of the same kind by a closed subspace, the quotient
map lifts bounded sets. The kernel is a limit subspace and itself a nuclear strict LF-space.
Deviation: For the quotient, strict LF plus nuclearity expresses the nuclear stage
condition by Remarks C.1.4.7 and C.1.5.12. -/
theorem liftsBoundedSets_quotient_of_nuclear_strictLF
    (h : IsInjectiveLCLimit j i) (hj : ∀ n, IsEmbedding (j n))
    (hFrechet : ∀ n, IsFrechetTVS (X n)) (hNuclear : ∀ n, IsNuclearTVS.{v} (X n))
    (F : Submodule ℂ E) (hF : IsClosed (F : Set E))
    (hQ : IsStrictLFSpace (E ⧸ F)) (hNuclearQ : IsNuclearTVS.{v} (E ⧸ F)) :
    LiftsBoundedSets F.mkQL ∧ IsLimitSubspace i F ∧ IsStrictLFSpace F ∧ IsNuclearTVS.{v} F := by
  have := hQ.1
  let K := limitStageKernel i F
  have hK (k : ℕ) : IsClosed (K k : Set (X k)) := (F.mkQL.comp (i k)).isClosed_ker
  let q := limitQuotientStageMap i F
  have hlim := isInjectiveLCLimit_quotientStages h F
  have hP (k : ℕ) := isFrechetTVS_quotient (hFrechet k) (K k) (hK k)
  have hlift : LiftsBoundedSets F.mkQL := by
    intro B hb
    obtain ⟨_, S, hS, hSF, hex, ht⟩ := hQ
    obtain ⟨n, A, ha, rfl⟩ := exists_bounded_stage_of_exhaustion S hS hSF hex ht hb
    have hinc (k : ℕ) : range (q k) ⊆ range (q (k+1)) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨limitQuotientTransition h F k x, DFunLike.congr_fun (hlim.compatible k) x⟩
    obtain ⟨k, v, hv⟩ := frechet_factorization hP q hlim.injective hinc hlim.exhaustive
      (hSF n) (S n).subtypeL
    obtain ⟨C, hc, hcover⟩ := liftsBoundedSets_mkQL_of_schwartz_frechet (hFrechet k)
      (isSchwartzTVS_of_isNuclearTVS (hNuclear k)) (K k) (hK k) _ (ha.image v)
    refine ⟨i k '' C, hc.image (i k), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, heq⟩ := hcover (mem_image_of_mem v hx)
    exact ⟨i k y, mem_image_of_mem _ hy,
      (congrArg (q k) heq).trans (DFunLike.congr_fun hv x)⟩
  have hsub := (isLimitSubspace_iff_liftsBoundedSets_of_nuclear h hj hFrechet hNuclear F hF).mpr hlift
  exact ⟨hlift, hsub, strictLFSpace_of_limitSubspace h hj hFrechet F hsub,
    isNuclearTVS_submodule (nuclear_of_injectiveLCLimit h hNuclear) F⟩

end Deferred

end RiemannMasullo
