module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b
import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b_PolarFreeExamples
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # The polar-free multiplication claim in §5.3.4 -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField
open scoped BigOperators

namespace RiemannMasullo

local notation "RealPlaces(" F ")" => {w : InfinitePlace F // InfinitePlace.IsReal w}
local notation "ComplexPlaces(" F ")" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

open Classical in
/-- Paper: Definition 5.3.4.1, p. 259. The function image of the tensor
product in (5.3.4.1) on the S-ideles is the span of the pure products with an
archimedean flat factor and multiplicative Schwartz–Bruhat finite factors. -/
def Printed.polarFreeTensorFunctions {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (r : (w : RealPlaces(F)) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : ComplexPlaces(F)) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)}) :
    Submodule ℂ ((SAdeleRing F S)ˣ → ℂ) :=
  Submodule.span ℂ {f | ∃ (h : archimedeanFlatSchwartz
      (ι := RealPlaces(F)) (κ := ComplexPlaces(F)))
    (k : ∀ v : S, SchwartzBruhat (v.val.adicCompletion F)ˣ),
    ∀ g, f g = h.val ((fun w ↦ (r w).val (g.val.1 w.val)),
      (fun w ↦ (c w).val (g.val.1 w.val))) *
        ∏ v : S, k v (Units.map ((Pi.evalRingHom _ v).comp (RingHom.snd _ _)).toMonoidHom g)}

/-- Paper: Lemma 5.3.4.2(3), p. 260. As printed: For every number field and finite
set of places containing the archimedean places, multiplication by any continuous
quasi-character trivial on the diagonal S-units preserves the polar-free tensor
functions of (5.3.4.1). This is the closure under multiplication clause, on the
S-ideles where the quasi-character is defined. The finite factors are those on
the multiplicative local groups. See `sAdelePolarFree_quasiCharacter_mul` and ERRATA F236. -/
def Printed.sAdelePolarFreeTensor_quasiCharacter_mul : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (r : (w : RealPlaces(F)) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : ComplexPlaces(F)) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
    (b : QuasiCharacter (SIdeleQuotient F S)) (f : (SAdeleRing F S)ˣ → ℂ),
    f ∈ Printed.polarFreeTensorFunctions S r c →
      (fun g ↦ b (QuotientGroup.mk g) * f g) ∈ Printed.polarFreeTensorFunctions S r c

private theorem polarFreeTensor_schwartz_bounded {G : Type} [CommGroup G]
    [TopologicalSpace G] (f : SchwartzBruhat G) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  let B : Submodule ℂ (G → ℂ) :=
    { carrier := {g | ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C}
      zero_mem' := ⟨0, fun _ ↦ by simp⟩
      add_mem' := by
        intro g h hg hh
        obtain ⟨A, hA⟩ := hg
        obtain ⟨C, hC⟩ := hh
        exact ⟨A + C, fun x ↦ (norm_add_le _ _).trans (add_le_add (hA x) (hC x))⟩
      smul_mem' := by
        intro c g hg
        obtain ⟨C, hC⟩ := hg
        exact ⟨‖c‖ * C, fun x ↦ by
          change ‖c • g x‖ ≤ _
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩ }
  have hB : schwartzBruhatSubmodule G ≤ B := by
    refine iSup_le fun a ↦ iSup_le fun e ↦ ?_
    rintro _ ⟨s, rfl⟩
    refine ⟨elementarySchwartzSeminorm (0, 0, 0, 0) s, fun x ↦ ?_⟩
    rw [schwartzBruhatStageRealization_apply]
    split_ifs
    · change (‖s _‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound s.val _).toReal
      apply ENNReal.toReal_mono (s.property.2 _).ne
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun y ↦ (‖s y‖₊ : ENNReal)) _
    · exact norm_zero.trans_le (apply_nonneg _ _)
  exact hB f.property

private theorem polarFreeTensor_bounded_on_slice {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (r : (w : RealPlaces(F)) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : ComplexPlaces(F)) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
    (z : ℕ → (SAdeleRing F S)ˣ) (hz : ∀ n, (z n).val.1 = 1)
    (f : (SAdeleRing F S)ˣ → ℂ) (hf : f ∈ Printed.polarFreeTensorFunctions S r c) :
    ∃ C : ℝ, ∀ n, ‖f (z n)‖ ≤ C := by
  classical
  unfold Printed.polarFreeTensorFunctions at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨h, k, hk⟩ := hf
    choose B hB using fun w : S ↦ polarFreeTensor_schwartz_bounded (k w)
    let x : (RealPlaces(F) → ℝ) × (ComplexPlaces(F) → ℂ) := (1, 1)
    refine ⟨‖h.val x‖ * ∏ w, max 0 (B w), fun n ↦ ?_⟩
    rw [hk, norm_mul, norm_prod, hz]
    have harch : ((fun w : RealPlaces(F) ↦ (r w).val ((1 : InfiniteAdeleRing F) w.val)),
        (fun w : ComplexPlaces(F) ↦ (c w).val ((1 : InfiniteAdeleRing F) w.val))) = x := by
      exact Prod.ext (funext fun _ ↦ map_one _) (funext fun _ ↦ map_one _)
    rw [harch]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun w _ ↦
        (hB w _).trans (le_max_right _ _))) (norm_nonneg _)
  | zero => exact ⟨0, fun _ ↦ by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA⟩ := hx
    obtain ⟨B, hB⟩ := hy
    exact ⟨A + B, fun n ↦ (norm_add_le _ _).trans (add_le_add (hA n) (hB n))⟩
  | smul a x _ hx =>
    obtain ⟨A, hA⟩ := hx
    exact ⟨‖a‖ * A, fun n ↦ by
      change ‖a • x (z n)‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hA n) (norm_nonneg _)⟩

open scoped NNReal in
open Filter in
/-- Paper: Lemma 5.3.4.2(3), p. 260. Take ℚ with the real and 2-adic places.
Use a flat bump equal to one at the archimedean identity. At the finite
place, take a unit-invariant factor with value q⁻ⁿ on the nonnegative
valuation shells and zero on the negative shells, where q is the residue
field cardinality. The sequence decays rapidly on the valuation lattice.
Twisting by the inverse square of the S-idelic norm changes the values
on the slice through the archimedean identity to qⁿ. Every finite slice of
a tensor function is a finite linear combination of bounded Schwartz–Bruhat
functions. -/
theorem Printed.sAdelePolarFreeTensor_quasiCharacter_mul_false :
    ¬ Printed.sAdelePolarFreeTensor_quasiCharacter_mul := by
  classical
  intro hall
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := {v}
  let w : S := ⟨v, Finset.mem_singleton_self v⟩
  have hw (u : S) : u = w := Subtype.ext (Finset.mem_singleton.mp u.property)
  let : Unique S := ⟨⟨w⟩, hw⟩
  let r (u : RealPlaces(ℚ)) :
      {e : u.val.Completion ≃+* ℝ // IsHomeomorph (e : u.val.Completion → ℝ)} :=
    ⟨InfinitePlace.Completion.ringEquivRealOfIsReal u.property,
      (InfinitePlace.Completion.isometryEquivRealOfIsReal u.property).toHomeomorph.isHomeomorph⟩
  let c (u : ComplexPlaces(ℚ)) :
      {e : u.val.Completion ≃+* ℂ // IsHomeomorph (e : u.val.Completion → ℂ)} :=
    ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex u.property,
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex u.property).toHomeomorph.isHomeomorph⟩
  obtain ⟨h, hh⟩ := exists_archimedeanFlatSchwartz_one (RealPlaces(ℚ)) (ComplexPlaces(ℚ))
  obtain ⟨π, k₀, hπ, hk₀⟩ := exists_polarFree_geometric_shell_test v
  let z (n : ℕ) : (SAdeleRing ℚ S)ˣ :=
    MulEquiv.prodUnits.symm (1, MulEquiv.piUnits.symm (Pi.mulSingle w (π ^ n)))
  have hz (n : ℕ) : (z n).val.1 = 1 := rfl
  let k (u : S) : SchwartzBruhat (u.val.adicCompletion ℚ)ˣ :=
    (hw u).symm ▸ k₀
  have hkw : k w = k₀ := by dsimp only [k]
  let f (g : (SAdeleRing ℚ S)ˣ) :=
    h.val ((fun u ↦ (r u).val (g.val.1 u.val)), (fun u ↦ (c u).val (g.val.1 u.val))) *
      ∏ u : S, k u (Units.map ((Pi.evalRingHom _ u).comp (RingHom.snd _ _)).toMonoidHom g)
  have hf : f ∈ Printed.polarFreeTensorFunctions S r c :=
    Submodule.subset_span ⟨h, k, fun _ ↦ rfl⟩
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    change 1 < (v.asIdeal.absNorm : ℝ)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans hq))
  have hπn (n : ℕ) :
      Units.map ((Pi.evalRingHom _ w).comp (RingHom.snd _ _)).toMonoidHom (z n) = π ^ n := by
    apply Units.ext
    change (Pi.mulSingle (M := fun u : S ↦ (u.val.adicCompletion ℚ)ˣ) w (π ^ n) w).val = (π ^ n).val
    rw [Pi.mulSingle_eq_same]
  have hfz (n : ℕ) : f (z n) = (q : ℂ)⁻¹ ^ n := by
    change h.val ((fun u ↦ (r u).val ((z n).val.1 u.val)),
        (fun u ↦ (c u).val ((z n).val.1 u.val))) *
      ∏ u : S, k u (Units.map ((Pi.evalRingHom _ u).comp (RingHom.snd _ _)).toMonoidHom (z n)) = _
    rw [hz, Fintype.prod_subsingleton _ w, hπn, hkw]
    have hm : ((fun u : RealPlaces(ℚ) ↦ (r u).val ((1 : InfiniteAdeleRing ℚ) u.val)),
        (fun u : ComplexPlaces(ℚ) ↦ (c u).val ((1 : InfiniteAdeleRing ℚ) u.val))) =
        ((1, 1) : (RealPlaces(ℚ) → ℝ) × (ComplexPlaces(ℚ) → ℂ)) :=
      Prod.ext (funext fun _ ↦ map_one _) (funext fun _ ↦ map_one _)
    rw [hm, hh, one_mul, hk₀]
    simp [q]
  let m := sIdeleQuotientNorm ℚ S
  let b : QuasiCharacter (SIdeleQuotient ℚ S) :=
    quasiCharacterNormTwist m (isProperMap_sIdeleQuotientNorm ℚ S).continuous 1 (-2)
  have hmod (n : ℕ) : (((m (QuotientGroup.mk (z n)) : ℝ≥0) : ℝ) : ℂ) =
      (q : ℂ)⁻¹ ^ n := by
    rw [show m (QuotientGroup.mk (z n)) = sIdeleNorm ℚ S (z n) from
      sIdeleQuotientNorm_mk ℚ S (z n)]
    let ev : ((SAdeleRing ℚ S)ˣ →* ℝ≥0ˣ) →* ℝ :=
      NNReal.toRealHom.toMonoidHom.comp ((Units.coeHom ℝ≥0).comp (MonoidHom.eval (z n)))
    change (ev (sIdeleNorm ℚ S) : ℂ) = _
    simp only [sIdeleNorm, map_mul, map_prod, map_pow]
    change (((∏ u : InfinitePlace ℚ, ‖(z n).val.1 u‖ ^ u.mult) *
      ∏ u : S, ‖(z n).val.2 u‖ : ℝ) : ℂ) = _
    rw [hz, Fintype.prod_subsingleton _ w]
    have hx : (z n).val.2 w = (π ^ n).val :=
      congrArg Units.val (hπn n)
    have harch (u : InfinitePlace ℚ) : ‖((1 : InfiniteAdeleRing ℚ) u)‖ = 1 :=
      norm_one
    simp only [harch, one_pow, Finset.prod_const_one, one_mul, hx,
      Units.val_pow_eq_pow_val, norm_pow, hπ, Complex.ofReal_pow, Complex.ofReal_inv]
    rfl
  obtain ⟨C, hC⟩ := polarFreeTensor_bounded_on_slice S r c z hz _
    (hall ℚ S r c b f hf)
  have hb (n : ℕ) : b (QuotientGroup.mk (z n)) * f (z n) = (q : ℂ) ^ n := by
    change (1 * (((m (QuotientGroup.mk (z n)) : ℝ≥0) : ℝ) : ℂ) ^ (-2 : ℂ)) * _ = _
    rw [one_mul, hmod, hfz, ← show ((-2 : ℤ) : ℂ) = -2 by norm_num,
      Complex.cpow_intCast, zpow_neg]
    change (((q : ℂ)⁻¹ ^ n) ^ (2 : ℕ))⁻¹ * (q : ℂ)⁻¹ ^ n = (q : ℂ) ^ n
    simp only [inv_pow, inv_inv]
    rw [pow_two, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one]
  have hlarge := (tendsto_pow_atTop_atTop_of_one_lt hq).eventually (eventually_gt_atTop C)
  obtain ⟨n, hn⟩ := hlarge.exists
  have hbnd := hC n
  change ‖b (QuotientGroup.mk (z n)) * f (z n)‖ ≤ C at hbnd
  rw [hb, norm_pow, Complex.norm_real, Real.norm_of_nonneg (le_of_lt (zero_lt_one.trans hq))] at hbnd
  exact (not_lt_of_ge hbnd) hn

end RiemannMasullo
