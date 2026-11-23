module
public import RiemannMasullo.Research.StripNuclearity.Local
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Projected trace class for smooth compact radial convolutions
-/

@[expose] public noncomputable section
open Function Filter MeasureTheory Set
open scoped Topology ContDiff Convolution ComplexConjugate

namespace RiemannMasullo.StripNuclearity

local notation "ν[" w "]" => (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal ((w : ℝ → ℝ) x))
local notation "H[" w "]" => Lp ℂ 2 ν[w]

private theorem nuclear_adjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    IsNuclearOperator T.adjoint := by
  have hTc := (mem_traceClassOperators_iff_isNuclearOperator T).mpr hT
  refine (mem_traceClassOperators_iff_isNuclearOperator T.adjoint).mp ?_
  change IsCompactOperator T.adjoint ∧ Summable (fun n ↦ approximationNumber T.adjoint n ^ (1 : ℝ))
  refine ⟨isCompactOperator_adjoint_of_compact T hTc.1, hTc.2.congr fun n ↦ ?_⟩
  congr 1
  by_cases hn : (n : Cardinal) < Module.rank ℂ H
  · exact approximationNumber_adjoint T hTc.1 n hn
  · have hle : Module.rank ℂ H ≤ (n : Cardinal) := le_of_not_gt hn
    have hzero (A : H →L[ℂ] H) : approximationNumber A n = 0 := by
      unfold approximationNumber
      refine le_antisymm ?_ (Real.sInf_nonneg ?_)
      · refine csInf_le ⟨0,?_⟩ ?_
        · rintro _ ⟨S,_,rfl⟩
          exact norm_nonneg _
        · exact ⟨A,(Submodule.rank_le _).trans hle, by simp⟩
      · rintro _ ⟨S,_,rfl⟩
        exact norm_nonneg _
    rw [hzero T,hzero T.adjoint]

/-- A compactly supported smooth radial convolution inherits trace class on
the spectral subspace from the projected two-sided Mellin resolvent. Its
weighted adjoint is resolved on the two tails, and the remaining compact
piece is nuclear by absolute Fourier inversion. -/
theorem nuclear_weighted_convolution_of_projected_resolvent {α s : ℝ} (hα : 0 ≤ α)
    {I : Set ℝ} (ho : IsOpen I) (hi : OrdConnected I) (hne : I.Nonempty) (c : ℝ)
    (hno : ∀ z : ℂ, z.re ∈ I → (c : ℂ)^2-z^2 ≠ 0)
    (κ : ℝ → ℂ) (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) :
    let w := intervalSobolevDensity (-α) α s
    ∀ (j : PositiveRealExponentialDecay I →L[ℂ] H[w]) (R P B₀ B₁ B₂ : H[w] →L[ℂ] H[w])
      (_ : ∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val)
      (_ : ∀ p, ∃ q : PositiveRealExponentialDecay I, R (j p) = j q ∧
        ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
          ((c : ℂ)^2-z^2)⁻¹ * mellin (fun t ↦ p.val (Real.log t)) z)
      (_ : IsNuclearOperator (R.adjoint.comp P))
      (_ : HasWeightedAdjointKernel w κ B₀)
      (_ : HasWeightedAdjointKernel w (deriv κ) B₁)
      (_ : HasWeightedAdjointKernel w (deriv (deriv κ)) B₂),
      IsNuclearOperator (B₀.adjoint.comp P) := by
  intro w j R P B₀ B₁ B₂ hj hr hN hB₀ hB₁ hB₂
  have hw : Continuous w := by
    unfold w intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun x ↦ Or.inl ?_)
    positivity
  have hp (x : ℝ) : 0 < w x := by
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨K,hK⟩ := hc.exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
  let T := max K 0 + 1
  have ht : 0 < T := by dsimp [T]; positivity
  have hrad {t : ℝ} (h : t ∈ tsupport κ) : |t| < T := by
    have hv : |t| ≤ K := by simpa [Real.norm_eq_abs] using hK t h
    dsimp [T]
    linarith [le_max_left K 0]
  let ap (x : ℝ) := Real.smoothTransition (x-T)
  let am (x : ℝ) := Real.smoothTransition (-x-T)
  let a0 (x : ℝ) := 1-ap x-am x
  have hpc : Continuous ap := Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)
  have hmc : Continuous am := Real.smoothTransition.continuous.comp (continuous_neg.sub continuous_const)
  have h0c : Continuous a0 := (continuous_const.sub hpc).sub hmc
  have h0s : HasCompactSupport a0 := by
    apply HasCompactSupport.intro (isCompact_Icc (a := -T-1) (b := T+1))
    intro x hx
    have hor : x < -T-1 ∨ T+1 < x := by
      by_contra! h
      exact hx ⟨h.1,h.2⟩
    rcases hor with h | h
    · simp [a0,ap,am,Real.smoothTransition.zero_of_nonpos (by linarith : x-T ≤ 0),
        Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ -x-T)]
    · simp [a0,ap,am,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x-T),
        Real.smoothTransition.zero_of_nonpos (by linarith : -x-T ≤ 0)]
  have h1 (x : ℝ) : |Real.smoothTransition x| ≤ 1 :=
    (abs_of_nonneg (Real.smoothTransition.nonneg x)).trans_le (Real.smoothTransition.le_one x)
  obtain ⟨Mp,hMp⟩ := exists_weight_multiplier hw hp ap hpc.measurable ⟨1,fun _ ↦ h1 _⟩
  obtain ⟨Mm,hMm⟩ := exists_weight_multiplier hw hp am hmc.measurable ⟨1,fun _ ↦ h1 _⟩
  let M0 := ContinuousLinearMap.id ℂ (H[w]) - Mp - Mm
  have hm0 (u : H[w]) : (M0 u : ℝ → ℂ) =ᵐ[volume] fun x ↦ (a0 x : ℂ)*u x := by
    have hbase : volume ≪ ν[w] := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
      (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp x)).ne')
    change ((u - Mp u - Mm u : H[w]) : ℝ → ℂ) =ᵐ[volume] _
    filter_upwards [hbase.ae_eq (Lp.coeFn_sub (u-Mp u) (Mm u)),hbase.ae_eq (Lp.coeFn_sub u (Mp u)),
      hMp u,hMm u] with x hsub hsub' hm hM
    simp only [hsub,Pi.sub_apply,hsub',hm,hM,a0,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  have h0N := nuclear_compactly_masked_adjoint hw hp κ hc hs B₀ hB₀ a0 h0c h0s M0 hm0
  have hpos (x y : ℝ) (hy : ap y ≠ 0) (hts : x-y ∈ tsupport κ) :
      (w x)⁻¹ = Real.exp (-(2*α)*x-(s/2)*Real.log (1+x^2)) := by
    have hy' : 0 < y-T := lt_of_not_ge (fun h ↦ hy (Real.smoothTransition.zero_of_nonpos h))
    have hx : 0 ≤ x := by linarith [(abs_lt.mp (hrad hts)).1]
    simpa only [ite_eq_left hx,neg_mul] using reciprocal_interval_weight_branches hα s x
  have hneg (x y : ℝ) (hy : am y ≠ 0) (hts : x-y ∈ tsupport κ) :
      (w x)⁻¹ = Real.exp (-(-2*α)*x-(s/2)*Real.log (1+x^2)) := by
    have hy' : 0 < -y-T := lt_of_not_ge (fun h ↦ hy (Real.smoothTransition.zero_of_nonpos h))
    have hx : ¬ 0 ≤ x := by linarith [(abs_lt.mp (hrad hts)).2]
    simpa only [ite_eq_right hx,neg_mul,neg_neg] using reciprocal_interval_weight_branches hα s x
  obtain ⟨Dp,hDp⟩ := exists_masked_resolvent_factor ho hi hne hno hw hp j R hj hr κ hc hs B₀ B₁ B₂
    hB₀ hB₁ hB₂ (2*α) s ap hpc Mp hMp hpos
  obtain ⟨Dm,hDm⟩ := exists_masked_resolvent_factor ho hi hne hno hw hp j R hj hr κ hc hs B₀ B₁ B₂
    hB₀ hB₁ hB₂ (-2*α) s am hmc Mm hMm hneg
  have hsum : B₀ = B₀.comp M0 + R.comp Dp + R.comp Dm := by
    rw [hDp,hDm]
    apply ContinuousLinearMap.ext
    intro u
    change B₀ u = B₀ (u - Mp u - Mm u) + B₀ (Mp u) + B₀ (Mm u)
    simp only [map_sub]
    abel
  have he : B₀.adjoint.comp P = (B₀.comp M0).adjoint.comp P + Dp.adjoint.comp (R.adjoint.comp P) +
      Dm.adjoint.comp (R.adjoint.comp P) := by
    conv_lhs => rw [hsum]
    simp only [map_add,ContinuousLinearMap.add_comp,ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.comp_assoc]
  rw [he]
  have hlocal := mul_mem_nuclearEndomorphisms_right P (⟨_,nuclear_adjoint _ h0N⟩ : nuclearEndomorphisms (H[w]))
  have hNp := mul_mem_nuclearEndomorphisms_left Dp.adjoint (⟨_,hN⟩ : nuclearEndomorphisms (H[w]))
  have hNm := mul_mem_nuclearEndomorphisms_left Dm.adjoint (⟨_,hN⟩ : nuclearEndomorphisms (H[w]))
  exact (nuclearEndomorphisms (H[w])).add_mem ((nuclearEndomorphisms (H[w])).add_mem hlocal hNp) hNm

end RiemannMasullo.StripNuclearity
