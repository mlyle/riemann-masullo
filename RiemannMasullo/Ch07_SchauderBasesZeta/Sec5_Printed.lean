module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec5
import all RiemannMasullo.Ch03_IdelicZeta.Sec2

/-! # False claims printed in §7.5 -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField Set
open scoped NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "U[" F "]" => PontryaginDual C[F]
local notation "ω[" F ", " χ "]" => (χ : U[F]).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* C[F])

/-- Paper: Theorem 7.5.0.1, p. 374.
The printed quotient map is a topological linear isomorphism with a translation
difference for every selected finite place. -/
def Printed.strongCoprimality : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (S : Finset V[F])
    (π : (v : V[F]) → (v.adicCompletion F)ˣ),
    (∀ v ∈ S, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val) →
    let ω := ω[F, χ]
    let j := (exists_strongCoprimalityThetaEmbedding ω).choose
    let D := strongCoprimalityDenominator ω S
    let E := strongCoprimalityDifferenceRange ω S π
    ∃ e : (StrongCoprimalityThetaSpace ω ⧸ D) ≃L[ℂ] (StrongCoprimalityDecaySpace ω ⧸ E),
      ∀ x : StrongCoprimalityThetaSpace ω,
        e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (j x)

/-- A continuous homomorphism into the reals kills every compact subgroup. -/
private theorem strongCoprimality_false_compact_le_ker {G : Type*} [CommGroup G]
    [TopologicalSpace G] (L : G →* Multiplicative ℝ) (hL : Continuous L)
    {k : Subgroup G} (hk : IsCompact (k : Set G)) : k ≤ L.ker := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp ((hk.image
    ((show Continuous (Multiplicative.toAdd : Multiplicative ℝ → ℝ) from continuous_id).comp
      hL)).isBounded)
  intro x hx
  rw [MonoidHom.mem_ker]
  by_contra h
  have hne : (L x).toAdd ≠ 0 := h
  have hxpos : 0 < |(L x).toAdd| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |(L x).toAdd|)
  have hbound := hC (L (x ^ n)).toAdd ⟨x ^ n, k.pow_mem hx n, rfl⟩
  rw [map_pow, toAdd_pow, nsmul_eq_mul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg n)] at hbound
  exact (not_lt_of_ge hbound) ((div_lt_iff₀ hxpos).mp hn)

open scoped ContDiff in
/-- On each fiber of an elementary group, a smooth function of a real-valued
continuous homomorphism is smooth in the cover coordinates. -/
private theorem strongCoprimality_false_contDiff_elementary {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
    (ψ : Multiplicative (ElementaryLieGroup m n r F) →* Multiplicative ℝ) (hψ : Continuous ψ)
    {H : ℝ → ℂ} (hH : ContDiff ℝ (∞) H) (z : Fin r → ℤ) (b : F) {p : ℕ∞} :
    ContDiff ℝ p (fun u ↦ H (ψ (Multiplicative.ofAdd (elementaryCover u z b))).toAdd) := by
  let c : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →+ ElementaryLieGroup m n r F :=
    { toFun := fun xt ↦ elementaryCover xt 0 0
      map_zero' := Prod.ext rfl (Prod.ext (funext fun _ ↦ AddCircle.coe_zero (1 : ℝ)) rfl)
      map_add' := fun x y ↦ Prod.ext rfl
        (Prod.ext (funext fun i ↦ AddCircle.coe_add (1 : ℝ) (x.2 i) (y.2 i)) (zero_add _).symm) }
  have hc : Continuous c :=
    continuous_fst.prodMk
      ((continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
        ((PiLp.continuous_apply 2 _ i).comp continuous_snd)).prodMk continuous_const)
  let ℓ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →+ ℝ :=
    (MonoidHom.toAdditive ψ).comp c
  have hℓ : Continuous ℓ := hψ.comp hc
  have hshift u : c u + elementaryCover 0 z b = elementaryCover u z b := by
    change elementaryCover u 0 0 + elementaryCover 0 z b = elementaryCover u z b
    refine Prod.ext (add_zero _) (Prod.ext (funext fun i ↦ ?_) (Prod.ext (zero_add _) (zero_add _)))
    change ((u.2 i : ℝ) : AddCircle (1 : ℝ)) + (((0 : EuclideanSpace ℝ (Fin n)) i : ℝ) :
      AddCircle (1 : ℝ)) = ((u.2 i : ℝ) : AddCircle (1 : ℝ))
    rw [show ((0 : EuclideanSpace ℝ (Fin n)) i : ℝ) = 0 from rfl, AddCircle.coe_zero, add_zero]
  have heq u : (ψ (Multiplicative.ofAdd (elementaryCover u z b))).toAdd =
      ℓ u + (ψ (Multiplicative.ofAdd (elementaryCover 0 z b))).toAdd := by
    rw [← hshift u, ofAdd_add, map_mul, toAdd_mul]
    rfl
  rw [show (fun u ↦ H (ψ (Multiplicative.ofAdd (elementaryCover u z b))).toAdd) =
      fun u ↦ H (ℓ u + (ψ (Multiplicative.ofAdd (elementaryCover 0 z b))).toAdd) from
    funext fun u ↦ by rw [heq u]]
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
    Prod.continuousSMul
  have hlin : ContDiff ℝ p (fun u ↦ ℓ u) := (ℓ.toRealLinearMap hℓ).contDiff
  exact (hH.of_le (by exact_mod_cast le_top)).comp (hlin.add contDiff_const)

open scoped ContDiff in
/-- Multiplying a Bruhat `Cᵖ` function by a smooth function of a continuous real-valued
homomorphism keeps it Bruhat `Cᵖ`, with the same good subgroup. -/
private theorem strongCoprimality_false_bruhatContDiff_mul {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    {p : ℕ} {f : G → ℂ} (hf : IsBruhatContDiff p f)
    (L : G →* Multiplicative ℝ) (hL : Continuous L) {H : ℝ → ℂ} (hH : ContDiff ℝ (∞) H) :
    IsBruhatContDiff p (fun g ↦ f g * H (L g).toAdd) := by
  obtain ⟨k, hk, hinv, hdesc⟩ := hf
  have hker : k ≤ L.ker := strongCoprimality_false_compact_le_ker L hL hk.isCompact
  refine ⟨k, hk, fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · show f (h.val * x) * H (L (h.val * x)).toAdd = f x * H (L x).toAdd
    rw [hinv h x, map_mul, MonoidHom.mem_ker.mp (hker h.property), one_mul]
  · obtain ⟨f₀, hf₀, hcd⟩ := hdesc a ha
    let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
    let q : a.quotient →* Multiplicative ℝ :=
      QuotientGroup.lift N (L.comp a.val.1.subtype) (fun x hx ↦ hker (ha ▸ hx))
    have hq : Continuous q := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
      (hL.comp continuous_subtype_val)
    refine ⟨fun x ↦ f₀ x * H (q x).toAdd, fun x ↦ ?_, fun e z b ↦ ?_⟩
    · show f₀ (QuotientGroup.mk x) * H (q (QuotientGroup.mk x)).toAdd = f x.val * H (L x.val).toAdd
      rw [hf₀ x]
      rfl
    · exact (hcd e z b).mul (strongCoprimality_false_contDiff_elementary
        (q.comp e.equiv.symm.toMulEquiv.toMonoidHom)
        (hq.comp e.equiv.symm.continuous) hH z b)

open scoped ContDiff in
/-- A unitary character of the idele classes times a smooth compactly supported function of
the logarithm of the norm is a compactly supported Bruhat test. -/
private theorem strongCoprimality_false_characterNormTest (F : Type*) [Field F] [NumberField F]
    [T2Space C[F]] [LocallyCompactSpace C[F]]
    (ψ : U[F]) (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hHc : HasCompactSupport H) :
    ∃ φ : BruhatCompactSupport C[F],
      ∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : NNReal) : ℝ)) := by
  have hpos (x : C[F]) : (0 : ℝ) < ((ideleClassNorm F x : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  let L : C[F] →* Multiplicative ℝ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (Real.log ((ideleClassNorm F x : NNReal) : ℝ))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        rw [map_mul, Units.val_mul, NNReal.coe_mul,
          Real.log_mul (hpos x).ne' (hpos y).ne', ofAdd_add] }
  have hL : Continuous L := continuous_ofAdd.comp
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous)).log fun x ↦ (hpos x).ne')
  have hs : IsBruhatSmooth (fun x ↦ (ψ x : ℂ) * H (L x).toAdd) := fun p ↦
    strongCoprimality_false_bruhatContDiff_mul
      ((mem_bruhatSmoothSubmodule_iff _).mp (pontryaginDual_mem_bruhatSmooth ψ) p) L hL hH
  have hcs0 : HasCompactSupport (fun x : C[F] ↦ H (L x).toAdd) := by
    let E : ℝ → NNRealˣ := fun t ↦
      Units.mk0 (Real.exp t).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'
    have hE : Continuous E := Units.continuous_iff.mpr
      ⟨continuous_real_toNNReal.comp Real.continuous_exp,
        (continuous_real_toNNReal.comp Real.continuous_exp).inv₀ fun t ↦
          (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'⟩
    have hK : IsCompact (E '' tsupport H) := hHc.isCompact.image hE
    refine HasCompactSupport.intro ((isProperMap_ideleClassNorm F).isCompact_preimage hK)
      fun x hx ↦ image_eq_zero_of_notMem_tsupport fun hmem ↦ hx ⟨_, hmem, ?_⟩
    apply Units.ext
    change (Real.exp (Real.log _)).toNNReal = _
    rw [Real.exp_log (hpos x), Real.toNNReal_coe]
  exact ⟨(⟨_, (mem_bruhatSmoothSubmodule_iff _).mpr hs, hcs0.mul_left⟩ :
    bruhatCompactSupportSubmodule C[F]), fun _ ↦ rfl⟩


/-- The class of the idele equal to `-1` at one finite place and `1` elsewhere is
nontrivial: a principal idele with archimedean component one is one. -/
private theorem strongCoprimality_false_neg_one_ne (v : V[ℚ]) :
    IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (-1) ≠ 1 := by
  classical
  intro h
  obtain ⟨r, hr⟩ := (QuotientGroup.eq_one_iff _).mp h
  have hval := congrArg Units.val hr
  have hinf := congrArg (fun x : 𝔸[ℚ] ↦ x.1 Rat.infinitePlace) hval
  change algebraMap ℚ Rat.infinitePlace.Completion r.val = 1 at hinf
  have hr₁ : r.val = 1 := (algebraMap ℚ Rat.infinitePlace.Completion).injective
    (hinf.trans (map_one _).symm)
  have hfin := congrArg (fun x : 𝔸[ℚ] ↦ x.2 v) hval
  change algebraMap ℚ (v.adicCompletion ℚ) r.val =
    RestrictedProduct.mulSingle (fun w : V[ℚ] ↦ w.adicCompletionIntegers ℚ) v
      ((-1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) v at hfin
  rw [RestrictedProduct.mulSingle_eq_same, hr₁, map_one, Units.val_neg, Units.val_one] at hfin
  have : (1 : ℚ) = -1 := (algebraMap ℚ (v.adicCompletion ℚ)).injective
    (by simpa only [map_neg, map_one] using hfin)
  norm_num at this

/-- Paper: Theorem 7.5.0.1, p. 374.
Over ℚ take the even quadratic character modulo 5, S = {(5)}, and the uniformizer 5.
In the splitting of the idele classes by the positive norm, this character has value
one on the uniformizer class. Its nontrivial restriction to the 5-adic units makes
the local unit average zero on this isotype. Weil principal value then acts as the
identity, giving a zero source quotient. The χ-weighted Haar integral annihilates the
printed difference and is nonzero on the product of the inverse compact character
with exp(−(log t)²) in the positive norm coordinate t. Thus the target is nonzero. -/
theorem Printed.strongCoprimality_false : ¬ Printed.strongCoprimality := by
  classical
  intro hall
  let : T2Space C[ℚ] := (ideleGroup_quotient.{0, 0} ℚ).2.2.2.2.2.1
  let : LocallyCompactSpace C[ℚ] := (ideleGroup_quotient.{0, 0} ℚ).2.2.2.2.2.2.1
  let : SecondCountableTopology C[ℚ] :=
    letI : SecondCountableTopology (IdeleGroup (𝓞 ℚ) ℚ) := idele_secondCountable ℚ
    inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 ℚ) ℚ ⧸ IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ))
  let : MeasurableSpace C[ℚ] := borel _
  let : BorelSpace C[ℚ] := ⟨rfl⟩
  let μ := ideleClassTamagawaMeasure ℚ
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil ℚ).1
  let N : C[ℚ] → ℝ := fun g ↦ ((ideleClassNorm ℚ g : NNReal) : ℝ)
  have hNpos (g : C[ℚ]) : 0 < N g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hNc : Continuous N :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm ℚ).continuous)
  -- The place 3, a uniformizer at every place, and the uniformizer class at 3.
  let v : V[ℚ] := Rat.HeightOneSpectrum.primesEquiv.symm ⟨3, Nat.prime_three⟩
  have hU (w : V[ℚ]) := (Valued.v : Valuation (w.adicCompletion ℚ)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (w : V[ℚ]) → (w.adicCompletion ℚ)ˣ := fun w ↦
    Units.mk0 (hU w).choose (hU w).choose_spec.ne_zero
  have hπ : ∀ w ∈ ({v} : Finset V[ℚ]), Valuation.IsUniformizer
      (Valued.v : Valuation (w.adicCompletion ℚ) (WithZero (Multiplicative ℤ))) (π w).val :=
    fun w _ ↦ (hU w).choose_spec
  let γ := IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (π v)
  have hNγ : Real.log (N γ) ≠ 0 := by
    have hlt : ‖(π v).val‖ < 1 :=
      Valued.toNormedField.norm_lt_one_iff.mpr (hπ v (Finset.mem_singleton_self v)).val_lt_one
    have hN : N γ = ‖(π v).val‖ := by
      change (((ideleClassNorm ℚ γ : NNRealˣ) : NNReal) : ℝ) = _
      rw [ideleClassNorm_ofAdicCompletion]
      rfl
    rw [hN]
    exact (Real.log_neg (norm_pos_iff.mpr (π v).ne_zero) hlt).ne
  -- A character that is nontrivial on the local unit −1 at 3 and trivial on γ.
  let g₀ := IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (-1)
  have hNg₀ : N g₀ = 1 := by
    change (((ideleClassNorm ℚ g₀ : NNRealˣ) : NNReal) : ℝ) = _
    rw [ideleClassNorm_ofAdicCompletion]
    change ‖((-1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ = 1
    rw [Units.val_neg, Units.val_one, norm_neg, norm_one]
  obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_apply_ne_one (strongCoprimality_false_neg_one_ne v)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, Circle.exp θ = (ψ γ)⁻¹ := Circle.exp_surjective _
  let t := θ / Real.log (N γ)
  let ν : U[ℚ] :=
    { toFun := fun g ↦ Circle.exp (t * Real.log (N g))
      map_one' := by simp [N]
      map_mul' := fun g h ↦ by
        rw [show N (g * h) = N g * N h by simp [N], Real.log_mul (hNpos g).ne' (hNpos h).ne',
          mul_add, Circle.exp_add]
      continuous_toFun := Circle.exp.continuous.comp
        (continuous_const.mul (hNc.log fun g ↦ (hNpos g).ne')) }
  let χ : U[ℚ] := ψ * ν
  have hχγ : χ γ = 1 := by
    change ψ γ * Circle.exp (t * Real.log (N γ)) = 1
    rw [show t * Real.log (N γ) = θ from div_mul_cancel₀ θ hNγ, hθ, mul_inv_cancel]
  have hχg₀ : χ g₀ ≠ 1 := by
    change ψ g₀ * Circle.exp (t * Real.log (N g₀)) ≠ 1
    rwa [hNg₀, Real.log_one, mul_zero, Circle.exp_zero, mul_one]
  -- χ is ramified at 3, so the corrected theorem compares with no differences at all.
  have hram : ¬ (ideleClassNormTwist χ 0).IsUnramifiedAt v := by
    rw [HeckeCharacter.isUnramifiedAt_iff]
    intro h
    have h1 := h (-1)
    change (MulChar.ofUnitHom ((ideleClassNormTwist χ 0).toHomUnits.comp
      (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v))) ((-1 : (v.adicCompletion ℚ)ˣ) : _) = 1 at h1
    rw [MulChar.ofUnitHom_coe] at h1
    change (χ g₀ : ℂ) * (N g₀ : ℂ) ^ (0 : ℂ) = 1 at h1
    rw [Complex.cpow_zero, mul_one] at h1
    exact hχg₀ (Subtype.ext h1)
  have hT : ({v} : Finset V[ℚ]).filter (fun w ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt w) = ∅ := by
    simp [Finset.filter_singleton, hram]
  let ω := χ.comp
    (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm ℚ).ker →ₜ* C[ℚ])
  obtain ⟨e₁, -⟩ := RiemannMasullo.strongCoprimality χ {v} π hπ
  obtain ⟨e₂, -⟩ := hall ℚ χ {v} π hπ
  have hE₁ (y : StrongCoprimalityDecaySpace ω) : y ∈ strongCoprimalityDifferenceRange ω
      (({v} : Finset V[ℚ]).filter (fun w ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt w)) π :=
    (mem_strongCoprimalityDifferenceRange _ _ _ y).mpr ⟨y, by
      rw [hT]
      simp [strongCoprimalityDifference]⟩
  -- The source quotient is zero, so the printed target quotient is zero.
  have hsrc (x : StrongCoprimalityThetaSpace ω ⧸ strongCoprimalityDenominator ω {v}) : x = 0 := by
    apply e₁.injective
    rw [map_zero]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e₁ x)
    rw [← hy]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hE₁ y)
  have htgt (y : StrongCoprimalityDecaySpace ω) : y ∈ strongCoprimalityDifferenceRange ω {v} π := by
    have : (Submodule.Quotient.mk y : StrongCoprimalityDecaySpace ω ⧸
        strongCoprimalityDifferenceRange ω {v} π) = 0 := by
      rw [← e₂.apply_symm_apply (Submodule.Quotient.mk y), hsrc (e₂.symm _), map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mp this
  -- Integration against χ kills every difference, since χ is trivial on γ.
  have hmod := strongCoprimalityNorm_isModulation_surjective (F := ℚ)
  have hint (f : StrongCoprimalityDecaySpace ω) :
      MeasureTheory.Integrable (fun g ↦ f.val.val g * (χ g : ℂ)) μ := by
    simpa using (modulatedLogMoment_linearContinuous _ hmod.1 hmod.2 ω μ χ 0).1 f
  have hkill (f : StrongCoprimalityDecaySpace ω) :
      ∫ g, strongCoprimalityDifference {v} π f.val.val g * (χ g : ℂ) ∂μ = 0 := by
    let F := fun g ↦ f.val.val g * (χ g : ℂ)
    have hpt (g : C[ℚ]) : strongCoprimalityDifference {v} π f.val.val g * (χ g : ℂ) =
        F g - F (γ⁻¹ * g) := by
      rw [strongCoprimalityDifference_singleton_apply, sub_mul]
      congr 1
      simp only [F, map_mul, map_inv, hχγ, inv_one, one_mul]
      rfl
    simp_rw [hpt]
    rw [MeasureTheory.integral_sub (hint f) ((hint f).comp_mul_left γ⁻¹),
      MeasureTheory.integral_mul_left_eq_self (μ := μ) F γ⁻¹, sub_self]
  -- A compactly supported test of the right isotype on which the integral is positive.
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let H : ℝ → ℂ := fun y ↦ (b y : ℂ)
  have hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H := Complex.ofRealCLM.contDiff.comp b.contDiff
  obtain ⟨φ, hφ⟩ := strongCoprimality_false_characterNormTest ℚ χ⁻¹ H hH
    (b.hasCompactSupport.comp_left Complex.ofReal_zero)
  let m : C[ℚ] →ₜ* NNRealˣ := ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  have hχinv (x : C[ℚ]) : ((χ⁻¹ x : Circle) : ℂ) = ((χ x)⁻¹ : Circle) := rfl
  let f₀ : ModulatedExponentialDecay m univ :=
    ⟨φ.val, bruhatCompactSupport_le_modulatedExponentialDecay m univ hmod.1 hmod.2 φ.property⟩
  have hiso : f₀ ∈ modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω := by
    refine (mem_modulatedDecayIsotype_iff m ω univ _ f₀).mpr fun u x ↦ ?_
    change φ.val ((u.val)⁻¹ * x) = (χ u.val : ℂ) * φ.val x
    have hu1 : ideleClassNorm ℚ u.val = 1 := u.property
    have hNu : N ((u.val)⁻¹ * x) = N x := by
      simp [N, hu1]
    rw [hφ, hφ, show Real.log ((ideleClassNorm ℚ ((u.val)⁻¹ * x) : NNReal) : ℝ) =
      Real.log ((ideleClassNorm ℚ x : NNReal) : ℝ) from congrArg Real.log hNu]
    rw [hχinv, hχinv, map_mul, map_inv, mul_inv, inv_inv, Circle.coe_mul]
    change (χ u.val : ℂ) * _ * _ = (χ u.val : ℂ) * (_ * _)
    ring
  let h : StrongCoprimalityDecaySpace ω := ⟨f₀, hiso⟩
  have hpos : ∫ g, h.val.val g * (χ g : ℂ) ∂μ ≠ 0 := by
    have hpt (g : C[ℚ]) : h.val.val g * (χ g : ℂ) = ((b (Real.log (N g)) : ℝ) : ℂ) := by
      change φ.val g * _ = _
      rw [hφ]
      rw [mul_right_comm, hχinv, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_mul]
    simp_rw [hpt]
    rw [integral_complex_ofReal, Ne, Complex.ofReal_eq_zero]
    have hc : Continuous fun g ↦ b (Real.log (N g)) :=
      b.continuous.comp (hNc.log fun g ↦ (hNpos g).ne')
    have hcs : HasCompactSupport fun g ↦ b (Real.log (N g)) := by
      refine φ.property.2.mono fun g hg ↦ ?_
      rw [Function.mem_support] at hg ⊢
      rw [hφ]
      exact mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.mpr hg)
    refine (hc.integral_pos_of_hasCompactSupport_nonneg_ne_zero hcs (fun g ↦ b.nonneg)
      (x := 1) ?_).ne'
    rw [show N 1 = 1 by simp [N], Real.log_one, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact one_ne_zero
  obtain ⟨f, hf⟩ := (mem_strongCoprimalityDifferenceRange ω {v} π h).mp (htgt h)
  exact hpos ((congrArg (fun F : C[ℚ] → ℂ ↦ ∫ g, F g * (χ g : ℂ) ∂μ) hf).trans (hkill f))

/-- Paper: Remark 7.5.0.2, p. 379.
The printed strong dual is a Hausdorff quotient of a closed subspace of a finite
locally convex sum of rapidly decreasing sequence spaces. -/
def Printed.strongCoprimalityPrimaryQuotient_strongDual_subquotient : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ω : PontryaginDual (ideleClassNorm F).ker)
    (p : V[ℚ]),
    let S := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    ∃ n : ℕ, let E := Fin n → RapidDecaySequence 1
      ∃ (W : Submodule ℂ E) (D : Submodule ℂ W),
        IsClosed (W : Set E) ∧ IsClosed (D : Set W) ∧
          Nonempty (StrongDual ℂ (StrongCoprimalityQuotient ω S) ≃L[ℂ] (W ⧸ D))

/-- Applying each coordinate functional to a finite relation gives its coefficient. -/
private theorem primaryQuotient_not_finite_of_basis {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] {x : ℕ → X} {d : ℕ → StrongDual ℂ X} (hb : IsSchauderBasis x d) :
    ¬ FiniteDimensional ℂ X := by
  intro hfin
  apply Module.Finite.not_linearIndependent_of_infinite (R := ℂ) x
  refine linearIndependent_iff'.mpr fun s c h i hi ↦ ?_
  have hδ (j : ℕ) : d i (x j) = if i = j then 1 else 0 := hb.1 i j
  simpa [map_sum, hδ, hi] using congrArg (d i) h

/-- The quotient by a single expanding difference has infinitely many Fourier modes. -/
private theorem primaryQuotient_singleDifference_infinite {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (m : G →ₜ* NNRealˣ) (hm : IsModulation m)
    (hms : Function.Surjective m) (ω : PontryaginDual m.toMonoidHom.ker) (a : G)
    (ha : 1 < (m a).val) : ¬ FiniteDimensional ℂ
      (↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω) ⧸
        fullDecayDifferenceRange m hm hms ω [a]) := by
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let γ : Fin 1 → G := fun _ ↦ a
  have hγ (k : Fin 1) : 1 < (m (γ k)).val := ha
  have hcomm : ∃ t : ℝ, 0 < t ∧ ∀ k, ∃ r : ℚ, Real.log ((m (γ k)).val : ℝ) = (r : ℝ) * t :=
    ⟨_, Real.log_pos (NNReal.coe_lt_coe.mpr ha), fun _ ↦ ⟨1, by simp [γ]⟩⟩
  obtain ⟨σ⟩ := modulatedPeriodicMomentIndex_enumerable m hm hms ω γ hγ zero_lt_one
  obtain ⟨ψ, hb, _⟩ :=
    modulatedQuotientLogMoment_bases m hm hms ω γ hγ MeasureTheory.Measure.haar hcomm σ
  have hlist : List.ofFn γ = [a] := by simp [List.ofFn_succ, γ]
  rw [← hlist]
  exact primaryQuotient_not_finite_of_basis hb

/-- Over ℚ every primary set is a singleton, and the trivial character keeps its difference. -/
private theorem primaryQuotient_rat_infinite (p : V[ℚ]) :
    ¬ FiniteDimensional ℂ (StrongCoprimalityQuotient ω[ℚ, 1]
      (finite_nuclearityPlacesAbove (F := ℚ) p).toFinset) := by
  classical
  have hself (v : V[ℚ]) : v.under (𝓞 ℚ) = v := by
    apply HeightOneSpectrum.ext
    change Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) v.asIdeal = v.asIdeal
    have hid : algebraMap (𝓞 ℚ) (𝓞 ℚ) = RingHom.id _ := by ext; simp
    rw [hid, Ideal.comap_id]
  have hS : (finite_nuclearityPlacesAbove (F := ℚ) p).toFinset = {p} := by
    ext v
    rw [Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact (congrArg (· = p) (hself v)).to_iff
  rw [hS]
  have hU (v : V[ℚ]) := (Valued.v : Valuation (v.adicCompletion ℚ)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π (v : V[ℚ]) : (v.adicCompletion ℚ)ˣ := Units.mk0 (hU v).choose (hU v).choose_spec.ne_zero
  apply (not_finiteDimensional_strongCoprimalityQuotient_iff (1 : U[ℚ]) {p} π
    (fun v _ ↦ (hU v).choose_spec)).mpr
  have htriv : ideleClassNormTwist (1 : U[ℚ]) 0 = 1 := by
    ext g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hur : (ideleClassNormTwist (1 : U[ℚ]) 0).IsUnramifiedAt p := by
    rw [htriv, HeckeCharacter.isUnramifiedAt_iff]
    intro u
    simp
  rw [Finset.filter_singleton, ite_eq_left hur]
  let : T2Space C[ℚ] := (ideleGroup_quotient.{0, 0} ℚ).2.2.2.2.2.1
  let : LocallyCompactSpace C[ℚ] := (ideleGroup_quotient.{0, 0} ℚ).2.2.2.2.2.2.1
  let : SecondCountableTopology C[ℚ] := by
    let : SecondCountableTopology (IdeleGroup (𝓞 ℚ) ℚ) := idele_secondCountable ℚ
    exact inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 ℚ) ℚ ⧸ IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ))
  let m : C[ℚ] →ₜ* NNRealˣ := ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  let a := (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ p (π p))⁻¹
  -- As in the norm calculation of Sec5, the inverse uniformizer expands by the residue cardinality.
  have ha : 1 < (m a).val := by
    change 1 < (ideleClassNorm ℚ (_⁻¹)).val
    rw [map_inv, ideleClassNorm_ofAdicCompletion, Units.coe_map_inv]
    change 1 < ‖((π p)⁻¹).val‖₊
    apply NNReal.coe_lt_coe.mp
    simp only [NNReal.coe_one, coe_nnNorm, Units.val_inv_eq_inv_val, norm_inv]
    rw [norm_uniformizer_adicCompletion p (π p).val (hU p).choose_spec, inv_inv]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
  have hm := strongCoprimalityNorm_isModulation_surjective (F := ℚ)
  have hrange : strongCoprimalityDifferenceRange ω[ℚ, 1] {p} π =
      fullDecayDifferenceRange m hm.1 hm.2 ω[ℚ, 1] [a] := by
    refine Eq.trans ?_ (fullDecayDifferenceRange_eq_span m hm.1 hm.2 ω[ℚ, 1] [a]).symm
    simp only [strongCoprimalityDifferenceRange, strongCoprimalityDifference,
      Finset.toList_singleton, List.foldr_cons, List.foldr_nil, a]
    rfl
  rw [hrange]
  exact primaryQuotient_singleDifference_infinite m hm.1 hm.2 _ a ha

/-- A quotient of a closed subspace of a finite product of rapid sequence spaces is Baire. -/
private theorem primaryQuotient_sequence_model_baire {n : ℕ}
    (W : Submodule ℂ (Fin n → RapidDecaySequence 1))
    (hW : IsClosed (W : Set (Fin n → RapidDecaySequence 1))) (D : Submodule ℂ W) :
    BaireSpace (W ⧸ D) := by
  obtain ⟨_, _, hmet, hcomplete⟩ := rapidDecaySequence_isFrechet (r := 1)
  have : CompleteSpace (RapidDecaySequence 1) := by
    rwa [IsUniformAddGroup.rightUniformSpace_eq] at hcomplete
  have : (uniformity (RapidDecaySequence 1)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  have : TopologicalSpace.IsCompletelyMetrizableSpace W := hW.isCompletelyMetrizableSpace
  have : BaireSpace W := BaireSpace.of_completelyPseudoMetrizable
  exact D.isOpenQuotientMap_mkQ.baireSpace

/-- Paper: Remark 7.5.0.2, p. 379.
Over ℚ with trivial character and p = 2, the primary quotient is the smooth
periodic space for period log 2. Its Fourier sequence space has strong dual
consisting of polynomially growing sequences. This dual is meagre in itself:
the closed sets of sequences bounded by m(1 + |n|)^m, for m ≥ 1, cover it
and have empty interior. A closed subspace of a finite product of Schwartz
sequence spaces, quotiented by a closed subspace, is Fréchet and hence Baire. -/
theorem Printed.strongCoprimalityPrimaryQuotient_strongDual_subquotient_false :
    ¬ Printed.strongCoprimalityPrimaryQuotient_strongDual_subquotient := by
  intro h
  let p : V[ℚ] := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  obtain ⟨n, W, D, hW, _, ⟨e⟩⟩ := h ℚ ω[ℚ, 1] p
  have hF := strongCoprimalityPrimaryQuotient_nuclearFrechet.{0, 0} ω[ℚ, 1] p
  apply not_bairespace_strongDual _ hF.1 hF.2 (primaryQuotient_rat_infinite p)
  have : BaireSpace (W ⧸ D) := primaryQuotient_sequence_model_baire W hW D
  exact e.toHomeomorph.isOpenEmbedding.baireSpace

/-- Paper: Theorem 7.5.0.1, proof, equation (7.5.0.8), p. 377.
At each reciprocal Euler zero for a place in the primary set S₀ = Sₚ of
p. 376, the zeroth reflected Fourier jet defines a continuous linear functional
on the full homogeneous theta space. This is the assertion at order zero.
Analyticity at the evaluation point
expresses ordinary evaluation of the meromorphic continuation there.
See `strongCoprimalityFourierJet_mk`, `exists_strongCoprimalityFourierJet_full`
and ERRATA F142. -/
def Printed.strongCoprimalityFourierJet_zero_full : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (p : V[ℚ]) (S : Finset V[F]),
    let S₀ := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    S₀ ⊆ S → Subsingleton (CommRing.Pic ((S : Set V[F]).integer F)) →
      ideleClassNormTwist χ 0 ∈ unramifiedOutside F S →
      ∀ v ∈ S₀, ∀ s : ℂ, (finiteHeckeEulerFactor χ v s)⁻¹ = 0 →
        let ω := ω[F, χ]
        let q := (LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)).mkQ
        ∃ d : StrongDual ℂ (GlobalHomogeneousThetaSpace F ω),
          ∀ f : SchwartzBruhat (Multiplicative (𝔸[F])),
            let Z := fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f)
              (ideleClassNormTwist χ⁻¹ z)
            AnalyticAt ℂ Z (1 - s) ∧ d (q f) = Z (1 - s)

section

open Filter
open scoped Topology

local instance strongCoprimalityFourierJetFalseClassMeasurable : MeasurableSpace (IdeleClassGroup (𝓞 ℚ) ℚ) := borel _
local notation "zeroAdele" => Multiplicative.ofAdd (0 : 𝔸[ℚ])
/-- The trivial character has value one on every local unit. -/
private theorem strongCoprimalityFourierJet_false_restrict_one (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ) :
    (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) 0).restrict v u = 1 := by
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  change (1 : ℂ) * _ ^ (0 : ℂ) = 1
  rw [Complex.cpow_zero, mul_one]
/-- The trivial character is unramified at every finite place. -/
private theorem strongCoprimalityFourierJet_false_unramified (v : HeightOneSpectrum (𝓞 ℚ)) :
    (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) 0).IsUnramifiedAt v := by
  rw [HeckeCharacter.isUnramifiedAt_iff]
  intro u
  exact strongCoprimalityFourierJet_false_restrict_one v (Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom u)
/-- At exponent zero, the reciprocal Euler factor of the trivial character vanishes. -/
private theorem strongCoprimalityFourierJet_false_euler (v : HeightOneSpectrum (𝓞 ℚ)) :
    (finiteHeckeEulerFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) v 0)⁻¹ = 0 := by
  let val : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)) := Valued.v
  let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion ℚ)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  have hv : (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) 0).localValue v = 1 := strongCoprimalityFourierJet_false_restrict_one v u
  simp [finiteHeckeEulerFactor, strongCoprimalityFourierJet_false_unramified v, hv]
/-- A test nonzero at zero gives a reflected Fourier zeta function that is not analytic at one. -/
private theorem strongCoprimalityFourierJet_false_nonanalytic (f : SchwartzBruhat (Multiplicative (𝔸[ℚ]))) (hf : f zeroAdele ≠ 0) :
    ¬ AnalyticAt ℂ (fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f)
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)) 1 := by
  intro ha
  let ν := normOneIdeleClassTamagawaMeasure ℚ
  let : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  let : ν.IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  have hm : (ν univ).toReal ≠ 0 := by
    exact (ENNReal.toReal_pos (isOpen_univ.measure_pos ν Set.univ_nonempty).ne'
      isCompact_univ.measure_lt_top.ne).ne'
  have hc : ContinuousAt (fun s : ℂ ↦ globalIdelicZFunction f
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) s)) 0 := by
    have ha' : ContinuousAt (fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f)
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)) (1 - 0) := by
      simpa using ha.continuousAt
    have h := ha'.comp (by fun_prop : ContinuousAt (fun s : ℂ ↦ 1 - s) 0)
    have heq : (fun s : ℂ ↦ globalIdelicZFunction f
        (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) s)) =
        (fun s : ℂ ↦ globalIdelicZFunction (adeleSchwartzFourier f)
          (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) (1 - s))) := by
      funext s
      rw [globalIdelicZFunction_functionalEquation, dualQuasiCharacter_ideleClassNormTwist, inv_one]
    rw [heq]
    exact h
  have ht : Tendsto (fun s : ℂ ↦ s * globalIdelicZFunction f
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) s))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [Pi.mul_apply, id_eq, zero_mul] using
      (continuousAt_id.tendsto.mul hc.tendsto).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have he := tendsto_nhds_unique ht (globalIdelicZFunction_residue_zero f)
  exact (mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hm)) hf) he.symm
/-- Paper: Theorem 7.5.0.1, proof, equation (7.5.0.8), p. 377.
Take F = ℚ, χ = 1, the rational prime 2, and s = 0. Enlarge the primary
set S₀ to a finite set S with trivial S-ideal class group. The reciprocal
Euler factor vanishes at zero. If the reflected Fourier zeta function of
the standard adelic Gaussian were analytic at one, the functional equation
would make its original zeta function continuous at zero. Its nonzero
residue there contradicts this continuity. -/
theorem Printed.strongCoprimalityFourierJet_zero_full_false :
    ¬ Printed.strongCoprimalityFourierJet_zero_full := by
  intro h
  classical
  let p : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  let S₀ := (finite_nuclearityPlacesAbove (F := ℚ) p).toFinset
  let T := (eventually_trivial_sIdealClassGroup (F := ℚ)).choose
  let S := T ∪ S₀
  have hS : Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)) :=
    (eventually_trivial_sIdealClassGroup (F := ℚ)).choose_spec S Finset.subset_union_left
  have hp : p ∈ S₀ := by
    change p ∈ (finite_nuclearityPlacesAbove (F := ℚ) p).toFinset
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    apply HeightOneSpectrum.ext
    change Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) p.asIdeal = p.asIdeal
    have he : algebraMap (𝓞 ℚ) (𝓞 ℚ) = RingHom.id _ := by
      ext x
      simp
    rw [he, Ideal.comap_id]
  have hu : ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) 0 ∈
      unramifiedOutside ℚ S := fun v _ ↦ strongCoprimalityFourierJet_false_unramified v
  have hd := h ℚ 1 p S Finset.subset_union_right hS hu p hp 0 (strongCoprimalityFourierJet_false_euler p)
  let f := adelicStandardGaussian (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
  have hf : f zeroAdele ≠ 0 := by
    change adelicStandardGaussian _ (Multiplicative.ofAdd 0) ≠ 0
    rw [adelicStandardGaussian_trivial_zero]
    exact pow_ne_zero _ (inv_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  apply strongCoprimalityFourierJet_false_nonanalytic f hf
  simpa only [inv_one, sub_zero] using (hd.choose_spec f).1

end

end RiemannMasullo
