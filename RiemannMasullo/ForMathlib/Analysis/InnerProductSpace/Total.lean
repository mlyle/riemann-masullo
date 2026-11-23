module

public import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Total families in Hilbert tensor products and normed quotients

Compact characters span a dense subspace of Haar L². Tensoring a total family with an
arbitrary Hilbert factor preserves totality. Finite joint moment support gives a second
density criterion for a biorthogonal family in a normed quotient.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set UniformSpace
open scoped TensorProduct InnerProductSpace Topology ENNReal

namespace RiemannMasullo

/-- Physical compact characters are total in Haar L². -/
theorem dense_span_pontryaginDual_toLp {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [μ.IsHaarMeasure] :
    ∃ v : PontryaginDual K → Lp ℂ 2 μ, (Submodule.span ℂ (range v)).topologicalClosure = ⊤ ∧
      ∀ (χ : PontryaginDual K), (v χ : K → ℂ) =ᵐ[μ] fun k ↦ (χ k : ℂ) := by
  let r : PontryaginDual K →* C(K, ℂ) := {
    toFun χ := ⟨fun k ↦ (χ k : ℂ), continuous_subtype_val.comp χ.continuous⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let T := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  refine ⟨T ∘ r, ?_, fun χ ↦ (r χ).coeFn_toLp (p := 2) (𝕜 := ℂ) μ⟩
  have hd := ContinuousMap.toLp_denseRange ℂ μ ℂ (by simp : (2 : ℝ≥0∞) ≠ ⊤)
  have h := hd.topologicalClosure_map_submodule (dense_span_pontryaginDual r (fun _ _ ↦ rfl))
  rwa [Submodule.map_span, ← range_comp] at h

/-- Totality of the second tensor factor can be tested in the algebraic elementary tensors,
and hence in their Hilbert completion. -/
theorem mem_of_mem_tmul_dense_family {A B E J : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : E ≃L[ℂ] Completion (A ⊗[ℂ] B)) (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    (v : J → B) (hv : (Submodule.span ℂ (range v)).topologicalClosure = ⊤)
    (ht : ∀ (a : A) (j : J), U.symm ↑(a ⊗ₜ[ℂ] v j) ∈ S) :
    ∀ e, e ∈ S := by
  have hp (a : A) (b : B) : U.symm ↑(a ⊗ₜ[ℂ] b) ∈ S := by
    let T := U.symm.toContinuousLinearMap.comp (Completion.toComplL.comp (TensorProduct.mkL ℂ A B a))
    have hle : Submodule.span ℂ (range v) ≤ S.comap T.toLinearMap :=
      Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact ht a j)
    exact (Submodule.span ℂ (range v)).topologicalClosure_minimal hle (hS.preimage T.continuous)
      (hv.symm ▸ Submodule.mem_top : b ∈ (Submodule.span ℂ (range v)).topologicalClosure)
  let T := U.symm.toContinuousLinearMap.comp (Completion.toComplL : (A ⊗[ℂ] B) →L[ℂ] _)
  have htens (t : A ⊗[ℂ] B) : T t ∈ S := by
    induction t using TensorProduct.inductionOn with
    | tmul a b => exact hp a b
    | add u v hu hv => simpa only [map_add] using S.add_mem hu hv
  intro e
  have h : U.symm (U e) ∈ S := Completion.denseRange_coe.induction_on (U e)
    (show IsClosed {x | U.symm x ∈ S} from hS.preimage U.symm.continuous) htens
  simpa using h

/-- Vectors with finite joint moment support form a linear subspace. -/
theorem exists_submodule_finite_moment_support {E J : Type*} [AddCommGroup E] [Module ℂ E]
    (L : J → E →ₗ[ℂ] ℂ) :
    ∃ S : Submodule ℂ E, (S : Set E) = {x | (support fun j ↦ L j x).Finite} := by
  refine ⟨{ carrier := {x | (support fun j ↦ L j x).Finite}
            zero_mem' := by simp
            add_mem' := fun {x y} hx hy ↦ ?_
            smul_mem' := fun c x hx ↦ ?_ }, rfl⟩
  · apply (Set.Finite.union hx hy).subset
    intro j hj
    by_cases hxj : L j x = 0
    · right
      intro hyj
      apply hj
      change L j (x + y) = 0
      rw [map_add, hxj, show L j y = 0 from hyj, add_zero]
    · exact Or.inl hxj
  · apply Set.Finite.subset hx
    intro j hj hz
    exact hj (by change L j (c • x) = 0; rw [map_smul, show L j x = 0 from hz, smul_zero])

open scoped Classical in
/-- Finite moment support gives a finite interpolant modulo the joint kernel.
When such inputs are dense, the quotient images of single-coordinate
interpolants have dense span. -/
theorem dense_span_quotient_biorthogonal_of_finite_support
    {J E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q] (q : E →L[ℂ] Q) (hq : Surjective q)
    (v : J → E) (l : J → E →ₗ[ℂ] ℂ)
    (hv : ∀ i j, l j (v i) = if i = j then 1 else 0)
    (hk : ∀ x, (∀ j, l j x = 0) → q x = 0)
    (hd : Dense {x : E | (Function.support (fun j ↦ l j x)).Finite}) :
    Dense (Submodule.span ℂ (range (fun i ↦ q (v i))) : Set Q) := by
  classical
  apply hq.denseRange.dense_of_mapsTo q.continuous hd
  intro x hx
  let S := hx.toFinset
  let y := ∑ i ∈ S, l i x • v i
  have hly (j : J) : l j y = l j x := by
    change l j (∑ i ∈ S, _) = _
    simp only [map_sum, map_smul, hv, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq']
    by_cases hj : j ∈ S
    · simp [hj]
    · have hz : l j x = 0 := by
        by_contra hn
        exact hj (hx.mem_toFinset.mpr hn)
      simp [hj, hz]
  have hxy : q x = q y := sub_eq_zero.mp (by
    rw [← map_sub]
    exact hk _ fun j ↦ by rw [map_sub, hly, sub_self])
  rw [hxy]
  change q (∑ i ∈ S, l i x • v i) ∈ Submodule.span ℂ _
  rw [map_sum]
  exact Submodule.sum_mem _ fun i hi ↦ (q.map_smul _ _).symm ▸
    (Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i)))


end RiemannMasullo
