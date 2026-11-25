module

public import research.CubicDirichletDivisors
import Lean
import Mathlib.NumberTheory.LSeries.Injectivity
import all RiemannMasullo.ForMathlib.NumberTheory.NumberField.DedekindZeta.MultipleZero
import all research.CubicDirichletDivisors
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.StandardNorm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.OnePlaceBaseNorm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormLocalOrder

/-! # The cubic norm quotient at large primitive conductor

Paper: Proposition 10.2.2.2, pp. 446–447; the real-segment condition (#7485).
The premise is exactly finiteness for every basepoint choice on the splitting
field of X³ − 2. All primitive conductors above one threshold share a finite
set of lines for positive quotient divisors, and a single zero-free right
margin at every height. Both conclusions are conditional on that premise.

fpet19 established the conductor-uniform consequence mathematically in
mccorvie/riemann-masullo#7485 (issuecomment-7148696977). The component cover
is willzh0's mccorvie/riemann-masullo#7504, commit 28d5be91102d668859dae92cdb6d0c200867aae0;
mrshu independently proved the same criterion in #7508. This file combines
the criterion with Naganori Yamaguchi's global class field theory (Nyll,
pinned at fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565) and the previously
verified rationally twisted cubic order formula in CubicDirichletDivisors.

The Nyll norm is used on the splitting field, where its image has finite
index. At any finite prime it has the right local character value and its
normalized absolute value is exactly the one used in the Hecke Euler factor.
Equality of two rational Hecke lifts of primitive Dirichlet characters forces
equality of their conductors by uniqueness of Dirichlet series and invariance
of the conductor under change of level.
-/

open NumberField IsDedekindDomain Set Filter Function Topology
open scoped NumberField.AdeleRing RestrictedProduct Topology NNReal
set_option quotPrecheck false
public noncomputable section

namespace RiemannMasullo.TwistedCubic.NormFibres
local notation "C[" E "]" => NumberField.IdeleClassGroup (𝓞 E) E
local notation "U[" E "]" => PontryaginDual (C[E])
local notation "Pr[" E "]" => HeightOneSpectrum (𝓞 E)

private def cftPullback (E : Type) [Field E] [NumberField E] (ψ : U[ℚ]) : U[E] :=
  ψ.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom ℚ E)

private theorem norm_eq_localOrder {E : Type} [Field E] [NumberField E]
    (v : Pr[E]) (x : (v.adicCompletion E)ˣ) :
    ‖x.val‖ = (v.asIdeal.absNorm : ℝ) ^ (-(FiniteIdeleGroup.localOrder v x).toAdd) := by
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ (by simp),
    FiniteIdeleGroup.localOrder_apply, neg_neg, NNReal.coe_zpow]
  rfl

private theorem cft_local (E : Type) [Field E] [NumberField E] (v : Pr[E]) (ψ : U[ℚ])
    (x : (v.adicCompletion E)ˣ) :
    ∃ y : ((v.under (𝓞 ℚ)).adicCompletion ℚ)ˣ,
      localAngular v (cftPullback E ψ) x = localAngular (v.under (𝓞 ℚ)) ψ y ∧
      ‖y.val‖ = ‖x.val‖ := by
  let p := v.under (𝓞 ℚ)
  let W : {w : Pr[E] // _root_.finitePlaceBelow (K := ℚ) w = p} := ⟨v, rfl⟩
  let : Algebra (p.adicCompletion ℚ) (v.adicCompletion E) :=
    (finitePlaceAdicCompletionMap ℚ E p W).toAlgebra
  let y := LocalFieldTheory.normUnits (p.adicCompletion ℚ) (v.adicCompletion E) x
  refine ⟨y, ?_, ?_⟩
  · exact congrArg ψ (_root_.IdeleGroup.ideleClassNorm_finitePlaceIdeleClass_eq_normUnits
      (K := ℚ) (L := E) p W x)
  · have ho : (FiniteIdeleGroup.localOrder p y).toAdd =
        (v.asIdeal.inertiaDeg (𝓞 ℚ) : ℤ) * (FiniteIdeleGroup.localOrder v x).toAdd :=
      FiniteIdeleGroup.localOrder_normUnits (K := ℚ) (L := E) p W x
    have : v.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
    have hn := Ideal.absNorm_pow_inertiaDeg p.asIdeal v.asIdeal
    rw [norm_eq_localOrder p y, norm_eq_localOrder v x, ho, ← hn, Nat.cast_pow, ← mul_neg,
      zpow_mul, zpow_natCast]


/-- A character of finite exponent is determined by its restriction to the unitary kernel
of a surjective positive norm. Every coset has an e-th power representative. -/
private theorem eq_of_eq_on_ker {G : Type*} [Group G] (ν : G →* ℝ≥0ˣ) (hν : Surjective ν)
    (φ ψ : G →* Circle) (e : ℕ) (he : 0 < e)
    (hφ : ∀ g, φ g ^ e = 1) (hψ : ∀ g, ψ g ^ e = 1)
    (hk : ∀ g, ν g = 1 → φ g = ψ g) : ∀ x, φ x = ψ x := by
  intro x
  let t := Units.map (NNReal.rpowMonoidHom (e : ℝ)⁻¹) (ν x)
  have ht : t ^ e = ν x := Units.ext (NNReal.rpow_inv_natCast_pow (ν x).val he.ne')
  obtain ⟨z, hz⟩ := hν t
  have hy : ν (x / z ^ e) = 1 := by rw [map_div, map_pow, hz, ht, div_self']
  simpa only [map_div, map_pow, hφ, hψ, div_one] using hk (x / z ^ e) hy

private theorem dual_pow_apply (χ : U[ℚ]) (e : ℕ) (y : C[ℚ]) :
    (χ ^ e) y = χ y ^ e :=
  ContinuousMonoidHom.pow_apply (χ : C[ℚ] →ₜ* Circle) e y

private theorem eval_pow_eq_one {χ : U[ℚ]} {e : ℕ} (h : χ ^ e = 1) (y : C[ℚ]) :
    χ y ^ e = 1 := by
  rw [← dual_pow_apply, h, PontryaginDual.one_apply]

private def cftComponent (E : Type) [Field E] [NumberField E] (χ : U[ℚ]) :
    PontryaginDual (RiemannMasullo.ideleClassNorm E).ker :=
  (cftPullback E χ).comp ⟨(RiemannMasullo.ideleClassNorm E).ker.subtype, continuous_subtype_val⟩

private theorem cft_restriction_eq (E : Type) [Field E] [NumberField E]
    {χ θ : U[ℚ]} (hχ : IsOfFinOrder χ) (hθ : IsOfFinOrder θ)
    (hcomp : cftComponent E χ = cftComponent E θ) : cftPullback E χ = cftPullback E θ := by
  obtain ⟨e,he,ha⟩ := isOfFinOrder_iff_pow_eq_one.mp hχ
  obtain ⟨f,hf,hb⟩ := isOfFinOrder_iff_pow_eq_one.mp hθ
  have a : χ ^ (e * f) = 1 := by rw [pow_mul, ha, one_pow]
  have b : θ ^ (e * f) = 1 := by rw [Nat.mul_comm, pow_mul, hb, one_pow]
  apply PontryaginDual.ext
  exact eq_of_eq_on_ker (RiemannMasullo.ideleClassNorm E) (ideleGroup_quotient.{_,0} E).2.2.2.2.2.2.2.2.2.1
    (cftPullback E χ).toMonoidHom (cftPullback E θ).toMonoidHom (e*f) (Nat.mul_pos he hf)
    (fun g ↦ eval_pow_eq_one a (_root_.ideleClassNorm ℚ E g))
    (fun g ↦ eval_pow_eq_one b (_root_.ideleClassNorm ℚ E g))
    (fun g hg ↦ congrArg (fun f : PontryaginDual (RiemannMasullo.ideleClassNorm E).ker ↦ f ⟨g,hg⟩) hcomp)

private theorem cft_finite_exceptions (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (T : Finset (PontryaginDual (RiemannMasullo.ideleClassNorm E).ker)) :
    ∃ X : Finset U[ℚ], ∀ χ : U[ℚ], IsOfFinOrder χ → cftComponent E χ ∈ T → χ ∈ X := by
  classical
  let H := (_root_.ideleClassNorm ℚ E).range
  let Q := C[ℚ] ⧸ H
  let : DiscreteTopology Q :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotient_discreteTopology (K := ℚ) (L := E)
  let q : C[ℚ] →ₜ* Q := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
  let repr (ω : PontryaginDual (RiemannMasullo.ideleClassNorm E).ker) : U[ℚ] :=
    if h : ∃ χ : U[ℚ], IsOfFinOrder χ ∧ cftComponent E χ = ω then h.choose else 1
  let exceptions (ω : PontryaginDual (RiemannMasullo.ideleClassNorm E).ker) :=
    (Finset.univ : Finset (PontryaginDual Q)).image (fun φ ↦ (φ.comp q : U[ℚ]) * repr ω)
  refine ⟨T.biUnion exceptions,fun χ hχ ht ↦ Finset.mem_biUnion.mpr ⟨_,ht,?_⟩⟩
  let ω := cftComponent E χ
  have h : ∃ θ : U[ℚ], IsOfFinOrder θ ∧ cftComponent E θ = ω := ⟨χ,hχ,rfl⟩
  have hr : repr ω = h.choose := dite_eq_left h
  have hres := cft_restriction_eq E hχ h.choose_spec.1 h.choose_spec.2.symm
  let δ := χ / repr ω
  have hk : H ≤ δ.toMonoidHom.ker := by
    rintro _ ⟨g,rfl⟩
    change χ (_root_.ideleClassNorm ℚ E g) / (repr ω) (_root_.ideleClassNorm ℚ E g) = 1
    rw [hr]
    exact div_eq_one.mpr (congrArg (fun f : U[E] ↦ f g) hres)
  let φ : PontryaginDual Q := ⟨QuotientGroup.lift H δ.toMonoidHom hk, continuous_of_discreteTopology⟩
  apply Finset.mem_image.mpr
  refine ⟨φ, Finset.mem_univ _, ?_⟩
  change δ * repr ω = χ
  exact div_mul_cancel _ _


private theorem cft_unram (E : Type) [Field E] [NumberField E] (v : Pr[E]) (ψ : U[ℚ])
    (hu : (ideleClassNormTwist ψ 0).IsUnramifiedAt (v.under (𝓞 ℚ))) :
    (ideleClassNormTwist (cftPullback E ψ) 0).IsUnramifiedAt v := by
  apply (unram_iff _ _).mpr
  intro x hx
  obtain ⟨y,he,hn⟩ := cft_local E v ψ x
  exact he.trans ((unram_iff _ _).mp hu _ (hn.trans hx))

private theorem cft_good_coefficient (E : Type) [Field E] [NumberField E] (v : Pr[E]) (ψ : U[ℚ])
    (h : (ideleClassNormTwist ψ 0).IsUnramifiedAt (v.under (𝓞 ℚ))) :
    coefficient (cftPullback E ψ) v = weight ψ v.asIdeal.absNorm := by
  classical
  let val := (Valued.v : Valuation (v.adicCompletion E) (WithZero (Multiplicative ℤ)))
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let x := Units.mk0 (π : v.adicCompletion E) hπ.ne_zero
  let p := v.under (𝓞 ℚ)
  obtain ⟨y,he,hn⟩ := cft_local E v ψ x
  rw [weight_eq ψ _ p y (minFac_norm E v).symm
    (hn.trans (norm_uniformizer_adicCompletion v (π : v.adicCompletion E) hπ)) h]
  have hu := cft_unram E v ψ h
  unfold coefficient
  rw [ite_eq_left hu, hu.localValue_eq _ hπ]
  change (ideleClassNormTwist (cftPullback E ψ) 0).restrict v (x.val) = _
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  change (localAngular v (cftPullback E ψ) x : ℂ) * _ ^ (0 : ℂ) = _
  rw [Complex.cpow_zero, mul_one, he]

private theorem cft_order_relation
    (L k K : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    [Field k] [NumberField k] [Field K] [NumberField K]
    (hG : Nonempty ((L ≃ₐ[ℚ] L) ≃* Equiv.Perm (Fin 3)))
    (ιk : Nonempty (k →ₐ[ℚ] L)) (hkdeg : Module.finrank ℚ k = 2)
    (ιK : Nonempty (K →ₐ[ℚ] L)) (hKdeg : Module.finrank ℚ K = 3)
    (ψ : U[ℚ]) {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt (continuedCompletedHeckeL (cftPullback L ψ)) z +
      (2 : ℕ) * meromorphicOrderAt (continuedCompletedHeckeL ψ) z =
    meromorphicOrderAt (continuedCompletedHeckeL (normPullback k ψ)) z +
      (2 : ℕ) * meromorphicOrderAt (continuedCompletedHeckeL (normPullback K ψ)) z := by
  classical
  obtain ⟨T,hT⟩ : ∃ T : Finset (Pr[ℚ]), ideleClassNormTwist ψ 0 ∈ unramifiedOutside ℚ T :=
    Set.mem_iUnion.mp ((iUnion_unramifiedOutside ℚ).symm ▸ Set.mem_univ _)
  obtain ⟨l, hl⟩ := good_norms L T
  obtain ⟨a, ha⟩ := good_norms ℚ T
  obtain ⟨b, hb⟩ := good_norms k T
  obtain ⟨c, hc⟩ := good_norms K T
  let B := (l ∪ a) ∪ (b ∪ c)
  have hsub (n : ℕ) (hn : n ∉ B) : (n ∉ l ∧ n ∉ a) ∧ n ∉ b ∧ n ∉ c := by simpa only [B, Finset.mem_union, not_or] using hn
  have H := common_weight_order_relation L k K hG ιk hkdeg ιK hKdeg
    (cftPullback L ψ) (normPullback ℚ ψ) (normPullback k ψ) (normPullback K ψ) (weight ψ) B
    (fun v hv ↦ cft_good_coefficient L v ψ (hT _ (hl v (hsub _ hv).1.1)))
    (fun v hv ↦ good_coefficient ℚ v ψ (hT _ (ha v (hsub _ hv).1.2)))
    (fun v hv ↦ good_coefficient k v ψ (hT _ (hb v (hsub _ hv).2.1)))
    (fun v hv ↦ good_coefficient K v ψ (hT _ (hc v (hsub _ hv).2.2))) hz
  simpa only [pull_rat] using H

local notation "ord(" χ ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat

private theorem cft_quotient_multiple (L k K : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    [Field k] [NumberField k] [Field K] [NumberField K]
    (hG : Nonempty ((L ≃ₐ[ℚ] L) ≃* Equiv.Perm (Fin 3)))
    (ιk : Nonempty (k →ₐ[ℚ] L)) (hkdeg : Module.finrank ℚ k = 2)
    (ιK : Nonempty (K →ₐ[ℚ] L)) (hKdeg : Module.finrank ℚ K = 3)
    (ψ : U[ℚ]) (z : ℂ) (h₀ : 0 < z.re) (h₁ : z.re < 1)
    (hlt : ord(ψ, z) < ord(normPullback K ψ, z)) : 1 < ord(cftPullback L ψ, z) := by
  have ho := cft_order_relation L k K hG ιk hkdeg ιK hKdeg ψ h₀
  rw [strip_order (cftPullback L ψ) z h₀ h₁, strip_order ψ z h₀ h₁,
    strip_order (normPullback k ψ) z h₀ h₁, strip_order (normPullback K ψ) z h₀ h₁] at ho
  have he := congrArg WithTop.untop₀ ho
  change (ord(cftPullback L ψ, z) : ℤ) + 2 * ord(ψ, z) =
    (ord(normPullback k ψ, z) : ℤ) + 2 * ord(normPullback K ψ, z) at he
  omega

/-- From the real-segment hypothesis of Proposition 10.2.2.2 on the closure
alone, one finite set of lines covers the positive quotient divisor of
every finite-order rational twist outside one finite character set. -/
theorem all_order_quotient_lines
    (L k K : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    [Field k] [NumberField k] [Field K] [NumberField K]
    (hG : Nonempty ((L ≃ₐ[ℚ] L) ≃* Equiv.Perm (Fin 3)))
    (ιk : Nonempty (k →ₐ[ℚ] L)) (hkdeg : Module.finrank ℚ k = 2)
    (ιK : Nonempty (K →ₐ[ℚ] L)) (hKdeg : Module.finrank ℚ K = 3)
    (hreal : ∀ (χ : PontryaginDual (RiemannMasullo.ideleClassNorm L).ker → U[L]), IsSpectralBasepointChoice χ →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω, 1 < ord(χ ω, (σ : ℂ))}.Finite) :
    ∃ (X : Finset U[ℚ]) (S : Finset ℝ), ∀ (ψ : U[ℚ]) (z : ℂ),
      IsOfFinOrder ψ → z.re ∈ Ioo (1 / 2 : ℝ) 1 →
      ord(ψ, z) < ord(normPullback K ψ, z) → ψ ∈ X ∨ z.re ∈ S := by
  obtain ⟨T,S,hcov⟩ := (spectralStripJet_multiple_real_zeros_finite_iff_finite_cover (F := L)).mp hreal
  obtain ⟨X,hX⟩ := cft_finite_exceptions L T
  refine ⟨X,S,fun ψ z hf hz ho ↦ ?_⟩
  have hm := cft_quotient_multiple L k K hG ιk hkdeg ιK hKdeg ψ z (by linarith [hz.1]) hz.2 ho
  have h := hcov (cftPullback L ψ) z.re z.im hz (by simpa only [Complex.re_add_im] using hm)
  exact h.imp (hX ψ hf) id

private theorem level_eq_of_rationalLift_eq {N M : ℕ} [NeZero N] [NeZero M]
    {ξ : DirichletCharacter ℂ N} (hξ : ξ.IsPrimitive)
    {η : DirichletCharacter ℂ M} (hη : η.IsPrimitive)
    (h : rationalLift hξ = rationalLift hη) : N = M := by
  have hξL := (DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hξ).choose_spec.2.2
  have hηL := (DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hη).choose_spec.2.2
  have hseries : (fun x : ℝ ↦ LSeries (fun n : ℕ ↦ ξ n) x) =ᶠ[atTop]
      fun x ↦ LSeries (fun n : ℕ ↦ η n) x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht' : 1 < (t : ℂ).re := ht
    exact (hξL t ht').symm.trans ((congrArg (fun ψ ↦ finiteHeckeL ψ ⟨t,ht'⟩) h).trans (hηL t ht'))
  have hc (n : ℕ) (hn : n ≠ 0) : ξ (n : ZMod N) = η (n : ZMod M) :=
    LSeries.eq_of_LSeries_eventually_eq (by
      rw [DirichletCharacter.abscissaOfAbsConv_eq_one (NeZero.ne N) ξ]; exact EReal.coe_lt_top 1) (by
      rw [DirichletCharacter.abscissaOfAbsConv_eq_one (NeZero.ne M) η]; exact EReal.coe_lt_top 1) hseries hn
  have hchange : ξ.changeLevel (N.dvd_mul_right M) = η.changeLevel (M.dvd_mul_left N) := by
    apply MulChar.ext
    intro u
    let n := (u.val : ZMod (N * M)).val + N * M
    have hn : n ≠ 0 := Nat.ne_of_gt (Nat.add_pos_right _ (Nat.mul_pos (NeZero.pos N) (NeZero.pos M)))
    have hcast : (n : ZMod (N*M)) = u.val := by simp [n, Nat.cast_add, ZMod.natCast_val]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      ← hcast, ZMod.cast_natCast (N.dvd_mul_right M), ZMod.cast_natCast (M.dvd_mul_left N)]
    exact hc n hn
  exact hξ.symm.trans ((DirichletCharacter.conductor_changeLevel ξ (N.dvd_mul_right M)).symm.trans
    ((congrArg DirichletCharacter.conductor hchange).trans
      ((DirichletCharacter.conductor_changeLevel η (M.dvd_mul_left N)).trans hη)))

private def representingConductor (ψ : U[ℚ]) : ℕ := open Classical in
  if h : ∃ (N : ℕ) (_ : NeZero N) (ξ : DirichletCharacter ℂ N) (hξ : ξ.IsPrimitive),
      rationalLift hξ = ψ then h.choose else 0

private theorem representingConductor_rationalLift {N : ℕ} [NeZero N] {ξ : DirichletCharacter ℂ N}
    (hξ : ξ.IsPrimitive) : representingConductor (rationalLift hξ) = N := by
  classical
  have h : ∃ (M : ℕ) (_ : NeZero M) (η : DirichletCharacter ℂ M) (hη : η.IsPrimitive),
      rationalLift hη = rationalLift hξ := ⟨N,inferInstance,ξ,hξ,rfl⟩
  rw [representingConductor, dite_eq_left h]
  obtain ⟨hM,η,hη,he⟩ := h.choose_spec
  exact level_eq_of_rationalLift_eq hη hξ he

local instance : Fact (Irreducible cubicPoly) := ⟨cubicIrreducible⟩
local instance : NumberField cubicClosure := ⟨⟩

/-- Assuming the real-segment assertion of Proposition 10.2.2.2 on the
splitting field of X³ − 2, all primitive Dirichlet twists above one conductor
threshold have their positive quotient divisors on a single finite set of
lines in the open right half of the critical strip, at every height. -/
theorem high_conductor_primitive_cubic_lines
    (hreal : ∀ (χ : PontryaginDual (RiemannMasullo.ideleClassNorm cubicClosure).ker → U[cubicClosure]),
      IsSpectralBasepointChoice χ →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω, 1 < ord(χ ω, (σ : ℂ))}.Finite) :
    ∃ (B : ℕ) (S : Finset ℝ), ∀ (N : ℕ) (_ : NeZero N)
      (ξ : DirichletCharacter ℂ N) (hξ : ξ.IsPrimitive) (z : ℂ),
      B < N → z.re ∈ Ioo (1 / 2 : ℝ) 1 →
      0 < meromorphicOrderAt (twistedQuotient (K := cubicField) hξ) z → z.re ∈ S := by
  classical
  let k := (Polynomial.X ^ 2 + Polynomial.C (3 : ℚ)).SplittingField
  have : NumberField k := ⟨⟩
  have : IsGalois ℚ cubicClosure := IsGalois.of_separable_splitting_field cubicIrreducible.separable
  let b := AdjoinRoot.powerBasis (Polynomial.X_pow_sub_C_ne_zero (by decide : 0 < 3) (2 : ℚ))
  have hd : b.dim = 3 := by rw [AdjoinRoot.powerBasis_dim, Polynomial.natDegree_X_pow_sub_C]
  obtain ⟨ιK, ιk, hk⟩ := spectralLineJet_memLp_false_subfields cubicPoly rfl cubicIrreducible
  have G := spectralLineJet_memLp_false_cubicGalois cubicPoly rfl cubicIrreducible
  obtain ⟨X,S,hXS⟩ := all_order_quotient_lines cubicClosure k cubicField G ιk hk ιK (b.finrank.trans hd) hreal
  refine ⟨X.sup representingConductor,S,fun N _ ξ hξ z hbig hre hz ↦ ?_⟩
  let ψ := rationalLift hξ
  let θ := normPullback cubicField ψ
  have h₀ : 0 < z.re := by linarith [hre.1]
  have h₁ := hre.2
  have hf := (finiteHeckeL_exists_continuation θ).choose_spec
  have hq := (DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hξ).choose_spec.2.2
  have he : meromorphicOrderAt (DirichletCharacter.LFunction ξ) z =
      meromorphicOrderAt (continuedCompletedHeckeL ψ) z :=
    meromorphicOrderAt_finiteHeckeL_continuation ψ (meromorphic_dirichletLFunction ξ)
      (fun s ↦ (DirichletCharacter.LFunction_eq_LSeries ξ s.2).trans (hq s s.2).symm) h₀
  change 0 < meromorphicOrderAt ((finiteHeckeL_exists_continuation θ).choose / DirichletCharacter.LFunction ξ) z at hz
  rw [meromorphicOrderAt_div (hf.1.meromorphicOn z (mem_univ _))
    (meromorphic_dirichletLFunction ξ z (mem_univ _)), he,
    meromorphicOrderAt_finiteHeckeL_continuation θ hf.1.meromorphicOn hf.2 h₀,
    strip_order ψ z h₀ h₁, strip_order θ z h₀ h₁] at hz
  have hi : (0 : ℤ) < (ord(θ, z) : ℤ) - ord(ψ, z) := WithTop.coe_lt_coe.mp hz
  have hlt : ord(ψ, z) < ord(θ, z) := by omega
  have hψ := (DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hξ).choose_spec.1
  apply (hXS ψ z hψ hre hlt).resolve_left
  intro hx
  exact (Nat.not_le_of_gt hbig) ((representingConductor_rationalLift hξ).symm ▸ Finset.le_sup (f := representingConductor) hx)

/-- The resulting zero-free interval is uniform in both the primitive conductor
and the imaginary part, after all common zeros in the quotient cancel. -/
theorem high_conductor_primitive_cubic_right_margin
    (hreal : ∀ (χ : PontryaginDual (RiemannMasullo.ideleClassNorm cubicClosure).ker → U[cubicClosure]),
      IsSpectralBasepointChoice χ →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω, 1 < ord(χ ω, (σ : ℂ))}.Finite) :
    ∃ (B : ℕ) (δ : ℝ), 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ (N : ℕ) (_ : NeZero N)
      (ξ : DirichletCharacter ℂ N) (hξ : ξ.IsPrimitive) (z : ℂ),
      B < N → 1 - δ < z.re → z.re < 1 → meromorphicOrderAt (twistedQuotient (K := cubicField) hξ) z ≤ 0 := by
  classical
  obtain ⟨B,S,hS⟩ := high_conductor_primitive_cubic_lines hreal
  let T := insert (1/2 : ℝ) ((S : Set ℝ) ∩ Ioo (1/2) 1)
  have hT : T.Finite := (S.finite_toSet.inter_of_left _).insert _
  obtain ⟨m,hm,hmax⟩ := Set.exists_max_image T id hT (insert_nonempty _ _)
  have hm₀ : (1/2 : ℝ) ≤ m := hmax _ (mem_insert _ _)
  have hm₁ : m < 1 := by
    rcases hm with rfl | h
    · norm_num
    · exact h.2.2
  refine ⟨B,1-m,by linarith,by linarith,fun N _ ξ hξ z hN hz h₁ ↦ ?_⟩
  by_contra! hp
  have hI : z.re ∈ Ioo (1/2 : ℝ) 1 := ⟨by linarith,h₁⟩
  have hle : z.re ≤ m := hmax _ (mem_insert_of_mem _ ⟨hS N inferInstance ξ hξ z hN hI hp,hI⟩)
  linarith

open Lean Elab Command

run_cmd auditRoot ``cft_local
run_cmd auditRoot ``cft_finite_exceptions
run_cmd auditRoot ``cft_order_relation
run_cmd auditRoot ``level_eq_of_rationalLift_eq
run_cmd auditRoot ``all_order_quotient_lines
run_cmd auditRoot ``high_conductor_primitive_cubic_lines
run_cmd auditRoot ``high_conductor_primitive_cubic_right_margin

end RiemannMasullo.TwistedCubic.NormFibres
