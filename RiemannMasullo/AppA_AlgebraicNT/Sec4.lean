module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2b
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# S-unit counting in the adelic unit box

Appendix A.4, pp. 562–565. The finite set parameter lists the finite places of S.
The archimedean places are included in `SAdeleRing`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open IsDedekindDomain NumberField
open scoped NNReal

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Oₛ" => Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Vₛ" => InfinitePlace F ⊕ S
local notation "sRank" => (Fintype.card (InfinitePlace F) + S.card - 1)
local notation "normℝ[" g "]" => ((Units.val (sIdeleNorm F S g) : ℝ≥0) : ℝ)
local notation "projectS" => Units.map (RingHom.toMonoidHom (adeleProjection F S))
local notation "outsideInclusion" =>
  Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F S)))
local notation "unitAtS" =>
  MonoidHom.comp projectS
    (MonoidHom.comp outsideInclusion (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S))))

/-- Paper: Theorem A.4.1.1(1), (A.4.1.1), p. 562. The archimedean unit box consists
of adeles whose normalized absolute value at each infinite place is at most one. -/
def infiniteAdeleUnitBox : Set (InfiniteAdeleRing F) :=
  {x | ∀ w : InfinitePlace F, ‖x w‖ ^ w.mult ≤ 1}

/-- Paper: Theorem A.4.1.1(1), (A.4.1.1), p. 562. A point of the box has ordinary
completion norm at most one at every infinite place. -/
theorem mem_infiniteAdeleUnitBox_iff (x : InfiniteAdeleRing F) :
    x ∈ infiniteAdeleUnitBox F ↔ ∀ w : InfinitePlace F, ‖x w‖ ≤ 1 := by
  change (∀ w : InfinitePlace F, ‖x w‖ ^ w.mult ≤ 1) ↔ _
  exact forall_congr' fun w ↦ pow_le_one_iff_of_nonneg (norm_nonneg _) w.mult_ne_zero

/-- Paper: Theorem A.4.1.1(1), p. 562. The archimedean unit box is compact. -/
theorem isCompact_infiniteAdeleUnitBox : IsCompact (infiniteAdeleUnitBox F) := by
  have hbox : infiniteAdeleUnitBox F =
      (Set.univ.pi fun w : InfinitePlace F ↦ Metric.closedBall (0 : w.Completion) 1 :
        Set (InfiniteAdeleRing F)) := by
    ext x
    rw [mem_infiniteAdeleUnitBox_iff]
    exact ⟨fun h w _ ↦ mem_closedBall_zero_iff.mpr (h w),
      fun h w ↦ mem_closedBall_zero_iff.mp (h w (Set.mem_univ _))⟩
  rw [hbox]
  refine isCompact_univ_pi fun w ↦ ?_
  have he := InfinitePlace.Completion.isometry_extensionEmbedding w
  simpa only [← he.preimage_closedBall] using
    he.isClosedEmbedding.isCompact_preimage (isCompact_closedBall (InfinitePlace.Completion.extensionEmbedding w 0) 1)

/-- Paper: Theorem A.4.1.1(1), p. 562. The archimedean unit box has nonempty interior. -/
theorem infiniteAdeleUnitBox_interior_nonempty : (interior (infiniteAdeleUnitBox F)).Nonempty := by
  let U : Set (InfiniteAdeleRing F) :=
    Set.univ.pi fun w : InfinitePlace F ↦ Metric.ball (0 : w.Completion) 1
  refine ⟨0, mem_interior.mpr ⟨U, fun x hx ↦ ?_, ?_, fun w _ ↦ Metric.mem_ball_self one_pos⟩⟩
  · rw [mem_infiniteAdeleUnitBox_iff]
    intro w
    have hw := hx w (Set.mem_univ _)
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact hw.le
  · exact isOpen_set_pi Set.finite_univ fun w _ ↦ Metric.isOpen_ball

/-- Paper: Theorem A.4.1.1(2), (A.4.1.2), p. 562. The test function is the indicator
of the archimedean unit box times the product of the finite-place integer-ring indicators. -/
def sAdeleUnitBoxIndicator (x : SAdeleRing F S) : ℝ :=
  (infiniteAdeleUnitBox F).indicator (fun _ ↦ (1 : ℝ)) x.1 *
    ∏ v : S, (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)).indicator
      (fun _ ↦ (1 : ℝ)) (x.2 v)

/-- Paper: Theorem A.4.1.1(2), (A.4.1.2), p. 562. The product indicator is one when
all coordinates have norm at most one and zero elsewhere. -/
theorem sAdeleUnitBoxIndicator_apply (x : SAdeleRing F S) :
    sAdeleUnitBoxIndicator F S x =
      if (∀ w : InfinitePlace F, ‖x.1 w‖ ≤ 1) ∧ (∀ v : S, ‖x.2 v‖ ≤ 1) then 1 else 0 := by
  have hv (v : S) : x.2 v ∈ (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)) ↔
      ‖x.2 v‖ ≤ 1 := by
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      Valued.toNormedField.norm_le_one_iff]
  change (infiniteAdeleUnitBox F).indicator (fun _ ↦ (1 : ℝ)) x.1 *
    ∏ v : S, (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)).indicator
      (fun _ ↦ (1 : ℝ)) (x.2 v) = _
  by_cases h1 : ∀ w : InfinitePlace F, ‖x.1 w‖ ≤ 1
  · by_cases h2 : ∀ v : S, ‖x.2 v‖ ≤ 1
    · rw [ite_eq_left ⟨h1, h2⟩, Set.indicator_of_mem ((mem_infiniteAdeleUnitBox_iff F x.1).2 h1),
        one_mul]
      exact Finset.prod_eq_one fun v _ ↦ Set.indicator_of_mem ((hv v).2 (h2 v)) _
    · rw [ite_eq_right fun h ↦ h2 h.2]
      push Not at h2
      obtain ⟨v, hv'⟩ := h2
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ v) ?_)
      exact Set.indicator_of_notMem (fun h ↦ (not_le.mpr hv') ((hv v).1 h)) _
  · rw [ite_eq_right fun h ↦ h1 h.1, Set.indicator_of_notMem
      (fun h ↦ h1 ((mem_infiniteAdeleUnitBox_iff F x.1).1 h)), zero_mul]

/-- Paper: Theorem A.4.1.1(2), p. 562. The product indicator has compact support. -/
theorem hasCompactSupport_sAdeleUnitBoxIndicator :
    HasCompactSupport (sAdeleUnitBoxIndicator F S) := by
  let K : Set (SAdeleRing F S) := infiniteAdeleUnitBox F ×ˢ
    Set.univ.pi fun v : S ↦ (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))
  have hK : IsCompact K := (isCompact_infiniteAdeleUnitBox F).prod
    (isCompact_univ_pi fun v ↦
      isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers (K := F) v.val))
  refine HasCompactSupport.intro hK fun x hx ↦ ?_
  rw [sAdeleUnitBoxIndicator_apply, ite_eq_right]
  rintro ⟨h1, h2⟩
  refine hx ⟨(mem_infiniteAdeleUnitBox_iff F x.1).2 h1, fun v _ ↦ ?_⟩
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
    ← Valued.toNormedField.norm_le_one_iff]
  exact h2 v

/-- Paper: Theorem A.4.1.1(2), p. 562. The product indicator is continuous off the
boundary of the product box.
Deviation: The continuity assertion specifies where the piecewise constant function is
continuous by excluding the frontier of its support. -/
theorem continuousAt_sAdeleUnitBoxIndicator (x : SAdeleRing F S)
    (hx : x ∉ frontier (Function.support (sAdeleUnitBoxIndicator F S))) :
    ContinuousAt (sAdeleUnitBoxIndicator F S) x := by
  set f := sAdeleUnitBoxIndicator F S
  have hcases : x ∉ closure (Function.support f) ∨ x ∈ interior (Function.support f) := by
    by_contra h
    push Not at h
    exact hx ⟨h.1, h.2⟩
  rcases hcases with hx | hx
  · have hf : (fun _ ↦ (0 : ℝ)) =ᶠ[nhds x] f := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      exact (Function.notMem_support.mp fun h ↦ hy (subset_closure h)).symm
    exact continuousAt_const.congr hf
  · have hf : (fun _ ↦ (1 : ℝ)) =ᶠ[nhds x] f := by
      filter_upwards [isOpen_interior.mem_nhds hx] with y hy
      have hy' : sAdeleUnitBoxIndicator F S y ≠ 0 := interior_subset hy
      change 1 = sAdeleUnitBoxIndicator F S y
      rw [sAdeleUnitBoxIndicator_apply] at hy' ⊢
      split_ifs at hy' ⊢ with h
      · rfl
      · exact absurd rfl hy'
    exact continuousAt_const.congr hf

/-- The S-logarithm turns products of S-ideles into sums. -/
private theorem sUnit_unitBox_count_bound_log_mul (g h : Iₛ) :
    sIdeleLog F S (g * h) = sIdeleLog F S g + sIdeleLog F S h := by
  funext v
  rcases v with v | v
  · have hne (a : Iₛ) : a.val.1 v ≠ 0 :=
      ((a.isUnit.map (RingHom.fst _ _)).map (Pi.evalRingHom _ v)).ne_zero
    change (v.mult : ℝ) * Real.log ‖g.val.1 v * h.val.1 v‖ =
      v.mult * Real.log ‖g.val.1 v‖ + v.mult * Real.log ‖h.val.1 v‖
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hne g)) (norm_ne_zero_iff.mpr (hne h)),
      mul_add]
  · have hne (a : Iₛ) : a.val.2 v ≠ 0 :=
      ((a.isUnit.map (RingHom.snd _ _)).map (Pi.evalRingHom _ v)).ne_zero
    change Real.log ‖g.val.2 v * h.val.2 v‖ = Real.log ‖g.val.2 v‖ + Real.log ‖h.val.2 v‖
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hne g)) (norm_ne_zero_iff.mpr (hne h))]

/-- The S-logarithm of a diagonal S-unit has coordinate sum zero. -/
private theorem sUnit_unitBox_count_bound_log_sum (u : Oₛˣ) :
    ∑ v, sIdeleLog F S (unitAtS u) v = 0 := by
  have h1 : sIdeleNorm F S (unitAtS u) = 1 :=
    MonoidHom.mem_ker.mp ((sIdeleNorm_spec F S).2 ⟨u, rfl⟩)
  rw [sIdeleLog_sum, h1]
  simp

/-- On S-ideles the box indicator is one exactly when every S-logarithmic coordinate is
nonpositive, and zero otherwise. -/
private theorem sUnit_unitBox_count_bound_indicator (h : Iₛ) :
    sAdeleUnitBoxIndicator F S h.val = if ∀ v, sIdeleLog F S h v ≤ 0 then 1 else 0 := by
  have hne₁ (w : InfinitePlace F) : 0 < ‖h.val.1 w‖ :=
    norm_pos_iff.mpr ((h.isUnit.map (RingHom.fst _ _)).map (Pi.evalRingHom _ w)).ne_zero
  have key : ((∀ w : InfinitePlace F, ‖h.val.1 w‖ ≤ 1) ∧ ∀ v : S, ‖h.val.2 v‖ ≤ 1) ↔
      ∀ v, sIdeleLog F S h v ≤ 0 := by
    constructor
    · rintro ⟨h1, h2⟩ (w | v)
      · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
          (Real.log_nonpos (norm_nonneg _) (h1 w))
      · exact Real.log_nonpos (norm_nonneg _) (h2 v)
    · intro hl
      refine ⟨fun w ↦ ?_, fun v ↦ ?_⟩
      · have hw := hl (Sum.inl w)
        change (w.mult : ℝ) * Real.log ‖h.val.1 w‖ ≤ 0 at hw
        have hm : (0 : ℝ) < w.mult := by exact_mod_cast w.mult_pos
        refine (Real.log_nonpos_iff (norm_nonneg _)).mp ?_
        by_contra hc
        push Not at hc
        linarith [mul_pos hm hc]
      · have hv := hl (Sum.inr v)
        change Real.log ‖h.val.2 v‖ ≤ 0 at hv
        exact (Real.log_nonpos_iff (norm_nonneg _)).mp hv
  rw [sAdeleUnitBoxIndicator_apply]
  by_cases hc : ∀ v, sIdeleLog F S h v ≤ 0
  · rw [ite_eq_left (key.mpr hc), ite_eq_left hc]
  · rw [ite_eq_right (mt key.mp hc), ite_eq_right hc]

/-- Diagonal S-units whose S-logarithm lies in a small ball are finite in number. -/
private theorem sUnit_unitBox_count_bound_finite :
    {u : Oₛˣ | ‖sIdeleLog F S (unitAtS u)‖ ≤ Real.log 2 / 2}.Finite := by
  let value (u : Oₛˣ) : F := u.val.val
  have hinj : Function.Injective value := fun _ _ h ↦ Units.ext (Subtype.ext h)
  let r : ℝ := Real.log 2 / 2
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine (Embeddings.finite_of_norm_le F ℂ (Real.exp r)).subset ?_
  rintro _ ⟨u, hu, rfl⟩
  have hne : value u ≠ 0 := (u.isUnit.map (Oₛ).val).ne_zero
  have hcoord (v : Vₛ) : sIdeleLog F S (unitAtS u) v ≤ r :=
    (le_abs_self _).trans ((norm_le_pi_norm (sIdeleLog F S (unitAtS u)) v).trans hu)
  refine ⟨?_, (InfinitePlace.le_iff_le (value u) (Real.exp r)).mp ?_⟩
  · -- At the selected finite places a norm less than two is at most one.
    have hval (v : HeightOneSpectrum (𝓞 F)) : v.valuation F (value u) ≤ 1 := by
      by_cases hv : v ∈ S
      · let x : v.adicCompletion F := algebraMap F _ (value u)
        have hxne : x ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hne
        have hxlog : Real.log ‖x‖ ≤ r := hcoord (Sum.inr ⟨v, hv⟩)
        have hxlt : ‖x‖ < 2 := (Real.log_lt_log_iff (norm_pos_iff.mpr hxne) (by norm_num)).mp
          (hxlog.trans_lt (by dsimp [r]; linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]))
        have hx : ‖x‖ ≤ 1 := le_of_not_gt fun h ↦
          (not_le_of_gt hxlt) (FinitePlace.two_le_norm_of_one_lt_norm (K := F) (v := v) x h)
        rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        exact Valued.toNormedField.norm_le_one_iff.mp hx
      · exact u.val.property v hv
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (value u) hval
    exact ha ▸ a.isIntegral_coe
  · intro v
    have hlog : (v.mult : ℝ) * Real.log (v (value u)) ≤ r := by
      have hv := hcoord (Sum.inl v)
      change (v.mult : ℝ) * Real.log ‖algebraMap F v.Completion (value u)‖ ≤ r at hv
      rw [InfinitePlace.coe_apply]
      simpa only [AbsoluteValue.Completion.algebraMap_def, AbsoluteValue.Completion.norm_coe,
        WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply, WithAbs.ofAbs_toAbs]
        using hv
    have hr : 0 ≤ r := div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
    have hm : (1 : ℝ) ≤ v.mult := by exact_mod_cast v.mult_pos
    apply (Real.log_le_iff_le_exp (v.pos_iff.mpr hne)).mp
    rw [mul_comm, ← le_div_iff₀ (lt_of_lt_of_le (by norm_num) hm)] at hlog
    exact hlog.trans (div_le_self hr hm)

/-- Paper: Theorem A.4.1.1, (A.4.1.3), p. 562. Uniformly for S-ideles of sufficiently
small S-idelic norm, the number of diagonal S-unit multiples in the unit box is bounded
by a constant times the absolute log norm to the power `|S| - 1`.
Deviation: The statement makes the finite support of the displayed sum explicit. -/
theorem sUnit_unitBox_count_bound :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ g : Iₛ, normℝ[g] < ε →
      let term := fun u : Oₛˣ ↦ sAdeleUnitBoxIndicator F S (unitAtS u * g).val
      (Function.support term).Finite ∧ ∑' u, term u ≤ C * |Real.log (normℝ[g])| ^ sRank := by
  classical
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  let i₀ : Vₛ := Sum.inl w₀
  have : Nonempty Vₛ := ⟨i₀⟩
  let n : ℕ := Fintype.card Vₛ
  have hn : 0 < n := Fintype.card_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let δ : ℝ := Real.log 2 / 2 / n
  have hδ : 0 < δ := by positivity
  have hnδ : n * δ = Real.log 2 / 2 := by
    change (n : ℝ) * (Real.log 2 / 2 / n) = _
    field_simp
  have hδle : δ ≤ Real.log 2 / 2 := by
    rw [← hnδ]
    exact le_mul_of_one_le_left hδ.le (by exact_mod_cast hn)
  let T : Set Oₛˣ := {u | ‖sIdeleLog F S (unitAtS u)‖ ≤ Real.log 2 / 2}
  have hT : T.Finite := sUnit_unitBox_count_bound_finite F S
  have : Finite T := hT.to_subtype
  have hcard : Nat.card {i : Vₛ // i ≠ i₀} = sRank := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      Fintype.card_sum, Fintype.card_coe]
  refine ⟨(1 / δ + 1) ^ sRank * Nat.card T + 1, Real.exp (-1), by positivity, Real.exp_pos _, ?_⟩
  intro g hg term
  obtain ⟨a, ha⟩ : ∃ a : Oₛˣ → Vₛ → ℝ, ∀ u, a u = sIdeleLog F S (unitAtS u) := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Vₛ → ℝ, ℓ = sIdeleLog F S g := ⟨_, rfl⟩
  have hnorm : 0 < normℝ[g] := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hlt : Real.log normℝ[g] < -1 := by
    have h := Real.log_lt_log hnorm hg
    rwa [Real.log_exp] at h
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = -Real.log normℝ[g] := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by linarith
  have habs : |Real.log normℝ[g]| = L := by rw [abs_of_neg (by linarith), hL]
  have hℓsum : ∑ i, ℓ i = -L := by rw [hℓ, sIdeleLog_sum, hL, neg_neg]
  have hasum (u : Oₛˣ) : ∑ i, a u i = 0 := by
    rw [ha]
    exact sUnit_unitBox_count_bound_log_sum F S u
  have hadiv (u u' : Oₛˣ) : a (u * u'⁻¹) = a u - a u' := by
    have h := sUnit_unitBox_count_bound_log_mul F S (unitAtS (u * u'⁻¹)) (unitAtS u')
    rw [← map_mul, inv_mul_cancel_right, ← ha, ← ha, ← ha] at h
    rw [h, add_sub_cancel_right]
  have hterm (u : Oₛˣ) : term u = if ∀ i, a u i + ℓ i ≤ 0 then 1 else 0 := by
    change sAdeleUnitBoxIndicator F S (unitAtS u * g).val = _
    rw [sUnit_unitBox_count_bound_indicator, sUnit_unitBox_count_bound_log_mul, ← ha, ← hℓ]
    rfl
  have hsupp (u : Oₛˣ) : u ∈ Function.support term ↔ ∀ i, a u i + ℓ i ≤ 0 := by
    rw [Function.mem_support, hterm]
    split_ifs with h
    · exact ⟨fun _ ↦ h, fun _ ↦ one_ne_zero⟩
    · exact ⟨fun h0 ↦ absurd rfl h0, fun h' ↦ absurd h' h⟩
  -- Every coordinate of a counted unit lies in an interval of length `L`.
  have hbox (u : Oₛˣ) (hu : u ∈ Function.support term) (i : Vₛ) :
      0 ≤ a u i + ℓ i + L ∧ a u i + ℓ i + L ≤ L := by
    have hb := (hsupp u).mp hu
    have hs : ∑ j, (a u j + ℓ j) = -L := by
      rw [Finset.sum_add_distrib, hasum, hℓsum, zero_add]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i] at hs
    have hrest : ∑ j : {j : Vₛ // j ≠ i}, (a u j + ℓ j) ≤ 0 :=
      Finset.sum_nonpos fun j _ ↦ hb j
    exact ⟨by linarith, by linarith [hb i]⟩
  let M : ℕ := ⌊L / δ⌋₊
  let φ : Oₛˣ → {i : Vₛ // i ≠ i₀} → ℕ := fun u i ↦ ⌊(a u i + ℓ i + L) / δ⌋₊
  have hφ (u : Oₛˣ) (hu : u ∈ Function.support term) (i : {i : Vₛ // i ≠ i₀}) :
      φ u i < M + 1 :=
    Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right (hbox u hu i).2 hδ.le))
  -- Two counted units with the same cell differ by a unit of small logarithm.
  have hfiber (u u' : Oₛˣ) (hu : u ∈ Function.support term) (hu' : u' ∈ Function.support term)
      (h : φ u = φ u') : u * u'⁻¹ ∈ T := by
    have hcoord (j : Vₛ) (hj : j ≠ i₀) : |a u j - a u' j| < δ := by
      have hk := congrFun h ⟨j, hj⟩
      change ⌊(a u j + ℓ j + L) / δ⌋₊ = ⌊(a u' j + ℓ j + L) / δ⌋₊ at hk
      have hy := div_nonneg (hbox u hu j).1 hδ.le
      have hy' := div_nonneg (hbox u' hu' j).1 hδ.le
      have h1 := Nat.floor_le hy
      have h2 := Nat.lt_floor_add_one ((a u j + ℓ j + L) / δ)
      have h1' := Nat.floor_le hy'
      have h2' := Nat.lt_floor_add_one ((a u' j + ℓ j + L) / δ)
      rw [hk] at h1 h2
      have hd : |(a u j + ℓ j + L) / δ - (a u' j + ℓ j + L) / δ| < 1 := by
        rw [abs_lt]
        constructor <;> linarith
      rwa [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ,
        show a u j + ℓ j + L - (a u' j + ℓ j + L) = a u j - a u' j by ring] at hd
    change ‖sIdeleLog F S (unitAtS (u * u'⁻¹))‖ ≤ Real.log 2 / 2
    rw [← ha, hadiv]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j ↦ ?_
    rw [Real.norm_eq_abs, Pi.sub_apply]
    by_cases hj : j = i₀
    · have hs : ∑ k, (a u k - a u' k) = 0 := by
        rw [Finset.sum_sub_distrib, hasum, hasum, sub_zero]
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀] at hs
      have he : a u i₀ - a u' i₀ = -∑ k : {k : Vₛ // k ≠ i₀}, (a u k - a u' k) := by linarith
      rw [hj, he, abs_neg]
      calc |∑ k : {k : Vₛ // k ≠ i₀}, (a u k - a u' k)|
          ≤ ∑ k : {k : Vₛ // k ≠ i₀}, |a u k - a u' k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : {k : Vₛ // k ≠ i₀}, δ := Finset.sum_le_sum fun k _ ↦ (hcoord k k.2).le
        _ = Fintype.card {k : Vₛ // k ≠ i₀} * δ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ n * δ := mul_le_mul_of_nonneg_right
          (by exact_mod_cast Fintype.card_subtype_le _) hδ.le
        _ = Real.log 2 / 2 := hnδ
    · exact (hcoord j hj).le.trans hδle
  let base : ({i : Vₛ // i ≠ i₀} → ℕ) → Oₛˣ := Function.invFunOn φ (Function.support term)
  have hbase (u : Oₛˣ) (hu : u ∈ Function.support term) :
      base (φ u) ∈ Function.support term ∧ φ (base (φ u)) = φ u :=
    Function.invFunOn_pos ⟨u, hu, rfl⟩
  let Ψ : Function.support term → ({i : Vₛ // i ≠ i₀} → Fin (M + 1)) × T := fun u ↦
    (fun i ↦ ⟨φ u i, hφ u u.2 i⟩,
      ⟨u * (base (φ u))⁻¹, hfiber u (base (φ u)) u.2 (hbase u u.2).1 (hbase u u.2).2.symm⟩)
  have hΨ : Function.Injective Ψ := by
    intro u u' h
    have h1 : φ u = φ u' := funext fun i ↦ congrArg Fin.val (congrFun (congrArg Prod.fst h) i)
    have h2 : (u : Oₛˣ) * (base (φ u))⁻¹ = u' * (base (φ u'))⁻¹ :=
      congrArg (fun p ↦ (p.2 : Oₛˣ)) h
    rw [h1] at h2
    exact Subtype.ext (mul_right_cancel h2)
  have hfin : (Function.support term).Finite := by
    have := Finite.of_injective Ψ hΨ
    exact Set.toFinite _
  refine ⟨hfin, ?_⟩
  have hcount : Nat.card (Function.support term) ≤ (M + 1) ^ sRank * Nat.card T := by
    have h := Nat.card_le_card_of_injective Ψ hΨ
    rwa [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin (M + 1)),
      Fintype.card_fin, hcard] at h
  have hsum : ∑' u, term u = Nat.card (Function.support term) := by
    rw [tsum_eq_sum (s := hfin.toFinset) fun u hu ↦ Function.notMem_support.mp
      (fun h ↦ hu (hfin.mem_toFinset.mpr h))]
    rw [Finset.sum_congr rfl fun u hu ↦ show term u = 1 by
      rw [hterm, ite_eq_left ((hsupp u).mp (hfin.mem_toFinset.mp hu))]]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_eq_card_finite_toFinset hfin]
  rw [hsum, habs]
  have hM : (M : ℝ) + 1 ≤ (1 / δ + 1) * L := by
    have h1 : (M : ℝ) ≤ L / δ := Nat.floor_le (div_nonneg (by linarith) hδ.le)
    rw [add_mul, one_mul, one_div_mul_eq_div]
    linarith
  have hLpow : 0 ≤ L ^ sRank := pow_nonneg (by linarith) _
  calc (Nat.card (Function.support term) : ℝ)
      ≤ ((M + 1) ^ sRank * Nat.card T : ℕ) := by exact_mod_cast hcount
    _ = ((M : ℝ) + 1) ^ sRank * Nat.card T := by push_cast; ring
    _ ≤ ((1 / δ + 1) * L) ^ sRank * Nat.card T := by gcongr
    _ = ((1 / δ + 1) ^ sRank * Nat.card T) * L ^ sRank := by rw [mul_pow]; ring
    _ ≤ ((1 / δ + 1) ^ sRank * Nat.card T + 1) * L ^ sRank :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hLpow

-- TODO(paper-gap): Page 562, note 3, proposes a remark about Connes without a statement.
-- TODO(paper-gap): Page 563, the image following (A.4.1.4) has discrete finite coordinates.
-- TODO(paper-gap): Page 563, (A.4.1.6) omits the torsion-fibre factor in the count.
-- TODO(paper-gap): Page 563, (A.4.1.7) can fail as a set equality. In ℚ(√2) take
-- the inert prime (3), the S-unit basis 3(1 + √2), 3 modulo torsion, and g₁ = 1.
-- At parallelotope coefficients (1/2, 1/2) the finite valuation is 1. Every basic
-- idele has finite valuation 0. Compare the domains modulo diagonal S-units.
-- TODO(paper-gap): Page 564, (A.4.1.8) pairs the normalized Haar measure with a Euclidean covolume.
-- TODO(paper-gap): Page 565, the proof of (A.4.1.9) assumes planar slicing preserves the face angles.
-- TODO(paper-gap): Page 565, the final constant omits the covolume and the counting error.

local notation "PicKernel" => MonoidHom.ker (CommRing.Pic.mapAlgebra (𝓞 F) Oₛ)
local notation "OutsideNormOne" => MonoidHom.ker (MonoidHom.comp (ideleNorm F) outsideInclusion)
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)

/-- At an infinite place the diagonal section has S-logarithm `log t` divided by the
number of infinite places. -/
private theorem sIdeleLog_basic_slice_subset_closedBall_diagonal_inl (t : ℝ≥0ˣ)
    (w : InfinitePlace F) :
    sIdeleLog F S (projectS (diagonalIdeleNormSection F t)) (Sum.inl w) =
      Real.log (t.val : ℝ) / Fintype.card (InfinitePlace F) := by
  classical
  have hcomp : (diagonalIdeleNormSection F t).val.1 w =
      (infinitePlaceRealPower F w ((w.mult : ℝ) * Fintype.card (InfinitePlace F))⁻¹ t).val := by
    let ψ : IdeleGroup (𝓞 F) F →* w.Completion :=
      (Pi.evalMonoidHom (fun v : InfinitePlace F ↦ v.Completion) w).comp
        ((MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
          (Units.coeHom (AdeleRing (𝓞 F) F)))
    change ψ (diagonalIdeleNormSection F t) = _
    simp only [diagonalIdeleNormSection, MonoidHom.finsetProd_apply, MonoidHom.comp_apply,
      map_prod]
    rw [Finset.prod_eq_single w]
    · exact Pi.mulSingle_eq_same _ _
    · intro v _ hv
      exact Pi.mulSingle_eq_of_ne' hv _
    · simp
  have ht : 0 < (t.val : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr t.ne_zero)
  have hnorm : ‖(diagonalIdeleNormSection F t).val.1 w‖ =
      (t.val : ℝ) ^ ((w.mult : ℝ) * Fintype.card (InfinitePlace F))⁻¹ := by
    rw [hcomp, ← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _), infinitePlaceRealPower_apply, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
  change (w.mult : ℝ) * Real.log ‖(diagonalIdeleNormSection F t).val.1 w‖ = _
  rw [hnorm, Real.log_rpow ht]
  have hm : (w.mult : ℝ) ≠ 0 := w.mult_coe_ne_zero
  have hc : (Fintype.card (InfinitePlace F) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

/-- At a finite place of S the diagonal section has S-logarithm zero. -/
private theorem sIdeleLog_basic_slice_subset_closedBall_diagonal_inr (t : ℝ≥0ˣ) (v : S) :
    sIdeleLog F S (projectS (diagonalIdeleNormSection F t)) (Sum.inr v) = 0 := by
  have h1 : (diagonalIdeleNormSection F t).val.2 v.val = 1 := by
    let ψ : IdeleGroup (𝓞 F) F →* v.val.adicCompletion F :=
      (RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) ↦ w.adicCompletion F)
        v.val).toMonoidHom.comp
        ((MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
          (Units.coeHom (AdeleRing (𝓞 F) F)))
    change ψ (diagonalIdeleNormSection F t) = 1
    simp only [diagonalIdeleNormSection, MonoidHom.finsetProd_apply, MonoidHom.comp_apply,
      map_prod]
    exact Finset.prod_eq_one fun w _ ↦ rfl
  change Real.log ‖(diagonalIdeleNormSection F t).val.2 v.val‖ = 0
  rw [h1, norm_one, Real.log_one]

/-- Paper: Claim A.4.1.2, p. 564. For fixed F and S there is a common radius multiplier
for every choice of fundamental domains and class representatives. For sufficiently
small basic ideles the translated slice lies in the ball of that radius times the
absolute log norm, uniformly in the basic idele and the class.
Deviation: The representatives project from global norm-one ideles that are units
outside S. A basic idele is the diagonal section times an archimedean domain point
with finite components in the local unit groups. -/
theorem sIdeleLog_basic_slice_subset_closedBall :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
      (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
      (bₛ : Module.Basis (Fin sRank) ℤ (Additive (Oₛˣ ⧸ CommGroup.torsion Oₛˣ)))
      (r : PicKernel → OutsideNormOne),
      (∀ i, ideleIdealClass F (outsideInclusion (r i).val) = i.val ∧
        projectS (outsideInclusion (r i).val) ∈
          Subgroup.subtype Nₛ '' sLocalIdeleFundamentalDomain F v₀ σ S bₛ) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ (t : ℝ≥0ˣ) (g₀ : Iₛ),
        Units.map (RingHom.fst _ _).toMonoidHom g₀ ∈
          Subgroup.subtype (infiniteIdeleNorm F).ker '' infiniteIdeleFundamentalDomain F b v₀ σ →
        (∀ v : S, g₀.val.2 v ∈ v.val.adicCompletionIntegers F ∧
          g₀.inv.2 v ∈ v.val.adicCompletionIntegers F) →
        let g := projectS (diagonalIdeleNormSection F t) * g₀
        normℝ[g] < ε → ∀ i : PicKernel,
          let gᵢ := projectS (outsideInclusion (r i).val)
          {x : EuclideanSpace ℝ Vₛ | (∑ v, x v) = 0 ∧
            ∀ v, x v + sIdeleLog F S (gᵢ * g) v ≤ 0} ⊆
            Metric.closedBall 0 (C₀ * |Real.log (normℝ[g])|) := by
  classical
  let n : ℕ := Fintype.card Vₛ
  have : Nonempty Vₛ := ⟨Sum.inl (Classical.arbitrary (InfinitePlace F))⟩
  have hn : 0 < n := Fintype.card_pos
  refine ⟨3 * n, by positivity, ?_⟩
  intro b v₀ σ bₛ r hr
  -- The S-logarithms of the class representatives lie in a bounded parallelotope.
  let B₁ : ℝ := ∑ k, ‖sIdeleLog F S (unitAtS (bₛ k).toMul.out)‖
  have hB₁ (i : PicKernel) :
      (∀ v, |sIdeleLog F S (projectS (outsideInclusion (r i).val)) v| ≤ B₁) ∧
      ∑ v, sIdeleLog F S (projectS (outsideInclusion (r i).val)) v = 0 := by
    obtain ⟨h, hmem, hh⟩ := (hr i).2
    have hh' : (h : Iₛ) = projectS (outsideInclusion (r i).val) := hh
    rw [← hh']
    obtain ⟨hpar, -⟩ := hmem
    refine ⟨fun v ↦ ?_, sRegulatorParallelotope_sum_zero F S bₛ _ hpar⟩
    obtain ⟨c, hc, hy⟩ := hpar
    rw [hy, ← Real.norm_eq_abs]
    refine (norm_le_pi_norm _ v).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc k).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hc k).2.le
  have hB₁nn : 0 ≤ B₁ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  -- The archimedean fundamental domain has bounded logarithms.
  obtain ⟨B₂, hB₂⟩ : ∃ B₂ : ℝ, ∀ h ∈ closure (infiniteIdeleFundamentalDomain F b v₀ σ),
      ‖infiniteIdeleLog F h.val‖ ≤ B₂ := by
    have hcont : Continuous fun h : (infiniteIdeleNorm F).ker ↦ ‖infiniteIdeleLog F h.val‖ :=
      ((infiniteIdeleLog_continuous F).comp continuous_subtype_val).norm
    obtain ⟨B, hB⟩ := (infiniteIdeleFundamentalDomain_precompact F b v₀ σ).bddAbove_image
      hcont.continuousOn
    exact ⟨B, fun h hh ↦ hB ⟨h, hh, rfl⟩⟩
  let B : ℝ := B₁ + max B₂ 0
  have hBnn : 0 ≤ B := add_nonneg hB₁nn (le_max_right _ _)
  refine ⟨Real.exp (-(B + 1)), Real.exp_pos _, ?_⟩
  intro t g₀ hg₀ hint g hg i gᵢ x hx
  -- The basic idele `g₀` has bounded logarithm with coordinate sum zero.
  obtain ⟨h₀, hh₀, hh₀'⟩ := hg₀
  have hh₀'' : h₀.val = Units.map (RingHom.fst _ _).toMonoidHom g₀ := hh₀'
  have hg₀fin (v : S) : sIdeleLog F S g₀ (Sum.inr v) = 0 := by
    have h1 : ‖g₀.val.2 v‖ ≤ 1 := by
      have h := (hint v).1
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers,
        ← Valued.toNormedField.norm_le_one_iff] at h
    have h2 : ‖g₀.inv.2 v‖ ≤ 1 := by
      have h := (hint v).2
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers,
        ← Valued.toNormedField.norm_le_one_iff] at h
    have h3 : ‖g₀.val.2 v‖ * ‖g₀.inv.2 v‖ = 1 := by
      rw [← norm_mul]
      have h := congrArg (fun z : SAdeleRing F S ↦ z.2 v) g₀.val_inv
      simp only [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply] at h
      rw [h, norm_one]
    have h4 : ‖g₀.val.2 v‖ = 1 :=
      le_antisymm h1 (by nlinarith [norm_nonneg (g₀.val.2 v), norm_nonneg (g₀.inv.2 v)])
    change Real.log ‖g₀.val.2 v‖ = 0
    rw [h4, Real.log_one]
  have hg₀log (v : Vₛ) : |sIdeleLog F S g₀ v| ≤ max B₂ 0 := by
    rcases v with w | v
    · change |infiniteIdeleLog F (Units.map (RingHom.fst _ _).toMonoidHom g₀) w| ≤ _
      rw [← hh₀'', ← Real.norm_eq_abs]
      exact ((norm_le_pi_norm _ w).trans (hB₂ h₀ (subset_closure hh₀))).trans
        (le_max_left _ _)
    · rw [hg₀fin, abs_zero]
      exact le_max_right _ _
  have hg₀sum : ∑ v, sIdeleLog F S g₀ v = 0 := by
    rw [Fintype.sum_sum_type, Finset.sum_eq_zero fun v _ ↦ hg₀fin v, add_zero]
    have h := infiniteIdeleLog_sum_zero F h₀
    rw [hh₀''] at h
    exact h
  -- The diagonal factor has logarithm `log t` spread over the infinite places.
  let lt : ℝ := Real.log (t.val : ℝ)
  let d := sIdeleLog F S (projectS (diagonalIdeleNormSection F t))
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by
    exact_mod_cast Fintype.card_pos
  have hdlog (v : Vₛ) : |d v| ≤ |lt| := by
    rcases v with w | v
    · change |sIdeleLog F S (projectS (diagonalIdeleNormSection F t)) (Sum.inl w)| ≤ _
      rw [sIdeleLog_basic_slice_subset_closedBall_diagonal_inl, abs_div, Nat.abs_cast]
      exact div_le_self (abs_nonneg _) hcard
    · change |sIdeleLog F S (projectS (diagonalIdeleNormSection F t)) (Sum.inr v)| ≤ _
      rw [sIdeleLog_basic_slice_subset_closedBall_diagonal_inr, abs_zero]
      exact abs_nonneg _
  have hdsum : ∑ v, d v = lt := by
    change ∑ v, sIdeleLog F S (projectS (diagonalIdeleNormSection F t)) v = Real.log (t.val : ℝ)
    rw [Fintype.sum_sum_type]
    simp only [sIdeleLog_basic_slice_subset_closedBall_diagonal_inl,
      sIdeleLog_basic_slice_subset_closedBall_diagonal_inr, Finset.sum_const_zero, add_zero,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  -- Logarithms of `g` and of `gᵢ * g`.
  have hglog : sIdeleLog F S g = d + sIdeleLog F S g₀ :=
    sUnit_unitBox_count_bound_log_mul F S _ _
  have hlogg : Real.log normℝ[g] = lt := by
    rw [← sIdeleLog_sum, hglog]
    simp only [Pi.add_apply, Finset.sum_add_distrib, hdsum, hg₀sum, add_zero]
  have hnorm : 0 < normℝ[g] := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hlt : lt < -(B + 1) := by
    have h := Real.log_lt_log hnorm hg
    rwa [Real.log_exp, hlogg] at h
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = -lt := ⟨_, rfl⟩
  have hLB : B + 1 < L := by linarith
  have habs : |Real.log normℝ[g]| = L := by rw [hlogg, abs_of_neg (by linarith), hL]
  have hlog_lt : |lt| = L := by rw [abs_of_neg (by linarith), hL]
  obtain ⟨hci, hcsum⟩ := hB₁ i
  have hℓ : sIdeleLog F S (gᵢ * g) = sIdeleLog F S gᵢ + (d + sIdeleLog F S g₀) := by
    rw [sUnit_unitBox_count_bound_log_mul, hglog]
  have hℓv (v : Vₛ) : |sIdeleLog F S (gᵢ * g) v| ≤ B + L := by
    rw [hℓ, Pi.add_apply, Pi.add_apply]
    have h1 := hci v
    have h2 := hdlog v
    have h3 := hg₀log v
    rw [hlog_lt] at h2
    calc |sIdeleLog F S gᵢ v + (d v + sIdeleLog F S g₀ v)|
        ≤ |sIdeleLog F S gᵢ v| + (|d v| + |sIdeleLog F S g₀ v|) :=
          (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
      _ ≤ B₁ + (L + max B₂ 0) := add_le_add h1 (add_le_add h2 h3)
      _ = B + L := by ring
  have hℓsum : ∑ v, sIdeleLog F S (gᵢ * g) v = -L := by
    rw [hℓ]
    simp only [Pi.add_apply, Finset.sum_add_distrib, hdsum, hg₀sum, add_zero]
    rw [show ∑ v, sIdeleLog F S gᵢ v = 0 from hcsum, zero_add, hL, neg_neg]
  -- Every coordinate of a point of the slice is at most `3 L` in absolute value.
  obtain ⟨hx0, hxle⟩ := hx
  have hxv (v : Vₛ) : |x v| ≤ 3 * L := by
    have hs : ∑ u, (x u + sIdeleLog F S (gᵢ * g) u) = -L := by
      rw [Finset.sum_add_distrib, hx0, hℓsum, zero_add]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ v] at hs
    have hrest : ∑ u : {u : Vₛ // u ≠ v}, (x u + sIdeleLog F S (gᵢ * g) u) ≤ 0 :=
      Finset.sum_nonpos fun u _ ↦ hxle u
    have h1 := hxle v
    have h2 := abs_le.mp (hℓv v)
    rw [abs_le]
    constructor <;> linarith
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, habs]
  have hL0 : 0 ≤ L := by linarith
  have hsq : ∑ v, ‖x v‖ ^ 2 ≤ (3 * n * L) ^ 2 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc ∑ v, ‖x v‖ ^ 2 ≤ ∑ _v : Vₛ, (3 * L) ^ 2 := Finset.sum_le_sum fun v _ ↦
          pow_le_pow_left₀ (norm_nonneg _) ((Real.norm_eq_abs _).trans_le (hxv v)) 2
      _ = n * (3 * L) ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (n : ℝ) ^ 2 * (3 * L) ^ 2 :=
          mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
      _ = (3 * n * L) ^ 2 := by ring
  calc √(∑ v, ‖x v‖ ^ 2) ≤ √((3 * n * L) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 3 * n * L := Real.sqrt_sq (by positivity)

end RiemannMasullo
