module

public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Exponential summability on lattices and their finite covers -/

@[expose] public noncomputable section

open Filter Function Set

namespace RiemannMasullo

/-- Exponential decay in the norm is summable on a discrete integer lattice. -/
theorem summable_lattice_exp_neg_mul_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {c : ℝ} (hc : 0 < c) :
    Summable (fun z : L ↦ Real.exp (-(c * ‖z‖))) := by
  classical
  let n := Module.finrank ℤ L + 1
  refine Summable.of_norm_bounded_eventually
    ((ZLattice.summable_norm_pow_inv L n (Nat.lt_succ_self _)).mul_left ((n.factorial : ℝ) / c ^ n)) ?_
  filter_upwards [eventually_cofinite_ne (0 : L)] with z hz
  have h0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h := Real.pow_div_factorial_le_exp _ (mul_nonneg hc.le h0.le) n
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_neg, inv_pow, ← div_eq_mul_inv]
  rw [inv_le_comm₀ (Real.exp_pos _) (by positivity)]
  rw [mul_pow] at h
  convert h using 1
  field_simp

private theorem summable_pullback_finite_kernel {H E : Type*} [AddCommGroup H] [AddCommGroup E]
    (l : H →+ E) [Fintype l.ker] (g : l.toIntLinearMap.range → ℝ) (hg : Summable g) (hn : ∀ z, 0 ≤ g z) :
    Summable (fun x : H ↦ g (l.toIntLinearMap.rangeRestrict x)) := by
  classical
  let L := l.toIntLinearMap.range
  let p : H → L := l.toIntLinearMap.rangeRestrict
  have hs : Surjective p := fun z ↦ z.property.elim fun x hx ↦ ⟨x, Subtype.ext hx⟩
  choose rep hrep using hs
  let j (x : H) : L × l.ker := (p x, ⟨x - rep (p x), by
    change l _ = 0
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val (hrep (p x)).symm⟩)
  have hj : Injective j := by
    intro x y h
    have hx : p x = p y := congrArg Prod.fst h
    have hh : x - rep (p x) = y - rep (p y) := congrArg (fun z : L × l.ker ↦ z.2.val) h
    rw [hx] at hh
    exact sub_left_inj.mp hh
  have hprod : Summable (fun z : L × l.ker ↦ g z.1) := by
    refine (summable_prod_of_nonneg (fun z ↦ hn z.1)).mpr ⟨fun _ ↦ .of_finite, ?_⟩
    simpa [tsum_fintype, nsmul_eq_mul] using hg.mul_left (Fintype.card l.ker : ℝ)
  exact hprod.comp_injective hj

/-- A proper homomorphism from a discrete additive group into a finite - dimensional real normed
space has finite kernel and discrete image. Exponential decay therefore pulls back to a summable
function on the source. -/
theorem summable_exp_neg_mul_norm_of_isProperMap {H E : Type*} [AddCommGroup H]
    [TopologicalSpace H] [DiscreteTopology H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (l : H →+ E) (hl : IsProperMap l) {c : ℝ} (hc : 0 < c) :
    Summable fun x : H ↦ Real.exp (-(c * ‖l x‖)) := by
  classical
  let L := l.toIntLinearMap.range
  let p : H → L := l.toIntLinearMap.rangeRestrict
  have hs : Surjective p := fun z ↦ z.property.elim fun x hx ↦ ⟨x, Subtype.ext hx⟩
  choose rep hrep using hs
  have hf := (hl.isCompact_preimage (isCompact_closedBall (0 : E) 1)).finite_of_discrete
  let : DiscreteTopology L := by
    apply discreteTopology_of_isOpen_singleton_zero
    refine isOpen_singleton_of_finite_mem_nhds 0 (s := Metric.closedBall 0 1)
      (Metric.closedBall_mem_nhds _ zero_lt_one) ?_
    refine (hf.image p).subset fun z hz ↦ ⟨rep z, ?_, hrep z⟩
    change l (rep z) ∈ Metric.closedBall 0 1
    change (p (rep z)).val ∈ Metric.closedBall 0 1
    rw [hrep]
    simpa [mem_closedBall_zero_iff] using hz
  have hf0 : (l.ker : Set H).Finite := hf.subset (fun x hx ↦ by
    change l x ∈ Metric.closedBall 0 1
    simp [show l x = 0 from hx])
  let : Fintype l.ker := hf0.fintype
  exact summable_pullback_finite_kernel l (fun z ↦ Real.exp (-(c * ‖z‖)))
    (summable_lattice_exp_neg_mul_norm L hc) (fun _ ↦ (Real.exp_pos _).le)

end RiemannMasullo
