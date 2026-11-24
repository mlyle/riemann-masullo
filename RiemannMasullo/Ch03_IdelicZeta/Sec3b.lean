module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec2
public import RiemannMasullo.AppC_LCTVS.Sec5b
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import all RiemannMasullo.Ch02_AdelicTheta.Sec2b
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import all RiemannMasullo.Ch02_AdelicTheta.Sec3
import all RiemannMasullo.Ch03_IdelicZeta.Sec3
import all RiemannMasullo.AppB_AnalyticNT.Sec2
import all RiemannMasullo.AppC_LCTVS.Sec5b
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gaussian.Schwartz
import Mathlib.RingTheory.Complex
import RiemannMasullo.ForMathlib.RingTheory.Trace.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import RiemannMasullo.ForMathlib.Analysis.Normed.Field.ProperSpace
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.VerticalStrip
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.CompactOpen
import RiemannMasullo.ForMathlib.Topology.Algebra.OpenSubgroup

/-!
# Partial Euler products and local zeta residues

Masullo, §3.3 from (3.3.1.25) through §3.3.2, pp. 134–141.
The exponent variables use the normalized local absolute values.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo
set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ" => SIdeleQuotient F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "ℬ(" K ")" => SchwartzBruhat (Multiplicative K)
local notation "test(" f ")" => (fun x ↦ f (Multiplicative.ofAdd x))
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "m∞(" w ")" => ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w :
  (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ)
local notation "m𝔭(" v ")" => (Units.map nnNormHom.toMonoidHom :
  (HeightOneSpectrum.adicCompletion F v)ˣ →* ℝ≥0ˣ)
local notation "h∞(" w ")" => continuous_infiniteLocalModule w
local notation "h𝔭(" v ")" => continuous_finiteLocalModule v
local notation "chartₛ(" χ ")" => quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ ((circleToComplex).comp χ)
local notation "emptyChart" => quasiCharacterNormTwist (G := SIdeleQuotient F ∅)
  (sIdeleQuotientNorm F ∅) (isProperMap_sIdeleQuotientNorm F ∅).continuous 1
local notation "chart∞[" w "," χ "]" =>
  quasiCharacterNormTwist m∞(w) h∞(w) ((circleToComplex).comp χ)
local notation "chart𝔭[" v "," χ "]" =>
  quasiCharacterNormTwist m𝔭(v) h𝔭(v) ((circleToComplex).comp χ)
local notation "rightHalf" => (Complex.re ⁻¹' Ioi (0 : ℝ))
local notation "vert(" σ "," t ")" => ((σ : ℂ) + (t : ℂ) * Complex.I)
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v))
local notation "diffExp(" v ")" => multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))
local notation "μ∞(" w ")" => infiniteLocalMultiplicativeTamagawaMeasure F w
local notation "μ𝔭(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v
local notation "ψ∞(" w ")" => (fun x ↦ adeleStandardCharacter F
  (@Pi.single _ _ _ (Classical.decEq _) w x, 0))
local notation "F∞(" w ")" => tamagawaFourier (infiniteLocalAdditiveTamagawaMeasure F w) ψ∞(w)
local notation "F𝔭(" v ")" => tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v)
  (finiteLocalStandardCharacter F v)

local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
local instance (v : Primes) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : Primes) : MeasurableSpace (v.adicCompletion F)ˣ := borel _

local notation "realModel(" hw ")" => InfinitePlace.Completion.ringEquivRealOfIsReal hw
local notation "complexModel(" hw ")" => InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
local notation "realShape[" hw "," c "," z "," a "]" => (∀ x : ℝˣ,
  c (Units.map (realModel(hw)).symm.toMonoidHom x) =
    (‖(x : ℝ)‖ : ℂ) ^ (z : ℂ) * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ (a : Fin 2).val)
local notation "complexShape[" hw "," c "," z "," r "]" => (∀ x : ℂˣ,
  c (Units.map (complexModel(hw)).symm.toMonoidHom x) =
    ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (z : ℂ) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ (r : ℤ))
local notation "unramified[" v "," c "]" => (∀ u : (HeightOneSpectrum.adicCompletionIntegers F v)ˣ,
  c (Units.map (HeightOneSpectrum.adicCompletionIntegers F v).subtype.toMonoidHom u) = 1)

/-- Paper: Equation (3.3.1.25), p. 134. A real local quasi-character has a
unique complex radial exponent and sign parity for its Euler factor. -/
theorem realLocalEulerParameters (w : InfinitePlace F) (hw : w.IsReal)
    (c : QuasiCharacter w.Completionˣ) :
    ∃! p : ℂ × Fin 2, realShape[hw, c, p.1, p.2] := by
  let e := (realModel(hw)).symm
  let i : ℝˣ →ₜ* w.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.units_map _⟩
  exact existsUnique_realUnits_quasiCharacter_parameters (c.comp i)

/-- Paper: Equation (3.3.1.25), p. 134. A complex local quasi-character has a
unique exponent for the squared absolute value and a unique angular weight. -/
theorem complexLocalEulerParameters (w : InfinitePlace F) (hw : w.IsComplex)
    (c : QuasiCharacter w.Completionˣ) :
    ∃! p : ℂ × ℤ, complexShape[hw, c, p.1, p.2] := by
  let e := (complexModel(hw)).symm
  let i : ℂˣ →ₜ* w.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.units_map _⟩
  exact existsUnique_complexUnits_quasiCharacter_parameters (c.comp i)

/-- Paper: Equation (3.3.1.25), p. 134. The infinite local Euler factor is the
real or complex gamma factor shifted by the sign parity or angular weight.
Deviation: As in §3.2.1, the complex factor uses half of Mathlib's Gammaℂ. -/
def infiniteLocalEulerFactor (w : InfinitePlace F) (c : QuasiCharacter w.Completionˣ) : ℂ :=
  open Classical in
  if hw : w.IsReal then
    let p := (realLocalEulerParameters w hw c).exists.choose
    Complex.Gammaℝ (p.1 + (p.2.val : ℂ))
  else
    let p := (complexLocalEulerParameters w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) c).exists.choose
    Complex.Gammaℂ (p.1 + (p.2.natAbs : ℂ) / 2) / 2

/-- Paper: Equation (3.3.1.25), p. 134. The Euler factor of a bare norm power
at a real place is the unshifted real gamma factor. -/
theorem infiniteLocalEulerFactor_real_norm (w : InfinitePlace F) (_hw : w.IsReal) (s : ℂ) :
    infiniteLocalEulerFactor w (chart∞[w, (1 : PontryaginDual w.Completionˣ)] s) =
      Complex.Gammaℝ s := by
  have hshape : realShape[_hw, (chart∞[w, (1 : PontryaginDual w.Completionˣ)] s), s,
      (0 : Fin 2)] := by
    intro x
    have hn : ‖((realModel(_hw)).symm (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
      (InfinitePlace.Completion.isometryEquivRealOfIsReal _hw).symm.isometry.norm_map_of_map_zero
        (map_zero (realModel(_hw)).symm) (x : ℝ)
    change (((1 : PontryaginDual w.Completionˣ)
      (Units.map (realModel(_hw)).symm.toMonoidHom x) : Circle) : ℂ) *
      (((m∞(w) (Units.map (realModel(_hw)).symm.toMonoidHom x) : ℝ≥0) : ℝ) : ℂ) ^ s = _
    simp [InfinitePlace.mult, _hw, hn]
  have h := (realLocalEulerParameters w _hw _).unique
    (realLocalEulerParameters w _hw _).exists.choose_spec (y₂ := (s, 0)) hshape
  simp only [infiniteLocalEulerFactor, _hw, ↓reduceDIte, h, Fin.val_zero, Nat.cast_zero, add_zero]

/-- Paper: Equation (3.3.1.25), p. 134. The finite local Euler factor of an
unramified character is the reciprocal of one minus its value at a uniformizer.
A ramified character contributes one. -/
def finiteLocalEulerFactor (v : Primes) (c : QuasiCharacter (v.adicCompletion F)ˣ) : ℂ :=
  open Classical in
  if unramified[v, c] then
    let h := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    (1 - c (Units.mk0 h.choose h.choose_spec.ne_zero))⁻¹
  else 1

/-- The geometric expression for a bare norm power also computes the
totalized Euler factor at exponents outside the convergence half-plane. -/
private theorem finiteEuler_norm_all (v : Primes) (s : ℂ) :
    finiteLocalEulerFactor v (chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s) =
      (1 - (q(v) : ℂ) ^ (-s))⁻¹ := by
  have hval (g : (v.adicCompletion F)ˣ) :
      chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s g = ((‖g.val‖ : ℝ) : ℂ) ^ s := by
    change (((1 : PontryaginDual (v.adicCompletion F)ˣ) g : Circle) : ℂ) *
      (((m𝔭(v) g : ℝ≥0) : ℝ) : ℂ) ^ s = _
    rw [PontryaginDual.one_apply, Circle.coe_one, one_mul]
    rfl
  have hunr : unramified[v, chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s] := by
    intro u
    rw [hval]
    have hu : ‖(Units.map (HeightOneSpectrum.adicCompletionIntegers F v).subtype.toMonoidHom u :
        (v.adicCompletion F)ˣ).val‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
          (a := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u)).mp
          ⟨u.val.property, u.inv.property⟩)
    rw [hu, Complex.ofReal_one, Complex.one_cpow]
  unfold finiteLocalEulerFactor
  rw [ite_eq_left hunr]
  dsimp only
  have harg : ((q(v) : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm
  rw [hval, Units.val_mk0, norm_uniformizer_adicCompletion v _
    (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec,
    Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, Complex.ofReal_natCast]

/-- Paper: Equation (3.3.1.25), p. 134. A bare norm power over a finite local
field gives the geometric Euler factor in the right half-plane. -/
theorem finiteLocalEulerFactor_norm (v : Primes) {s : ℂ} (hs : s ∈ rightHalf) :
    finiteLocalEulerFactor v (chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s) =
      (1 - (q(v) : ℂ) ^ (-s))⁻¹ :=
  finiteEuler_norm_all v s

/-- Paper: Equation (3.3.1.25), p. 134. The S-local Hecke L-function is the
product of the Euler factors of the restricted quasi-characters. -/
def sLocalHeckeL (c : QuasiCharacter Jₛ) : ℂ :=
  (∏ w : InfinitePlace F, infiniteLocalEulerFactor w (sLocalInfiniteRestriction w c)) *
    ∏ v : S, finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c)

/-- Paper: Equation (3.3.1.25), p. 134. For a bare norm power and no finite
places, the partial Euler product consists of the unshifted gamma factors. -/
theorem sLocalHeckeL_archimedean (s : ℂ) :
    sLocalHeckeL (emptyChart s) =
      Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces F *
        (Complex.Gammaℂ s / 2) ^ InfinitePlace.nrComplexPlaces F := by
  classical
  rw [sLocalHeckeL, Finset.univ_eq_attach, Finset.attach_empty, Finset.prod_empty, mul_one]
  have hfac (w : InfinitePlace F) :
      infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (emptyChart s)) =
        if w.IsReal then Complex.Gammaℝ s else Complex.Gammaℂ s / 2 := by
    have hval (g : w.Completionˣ) : sLocalInfiniteRestriction w (emptyChart s) g =
        (((m∞(w) g : ℝ≥0) : ℝ) : ℂ) ^ s :=
      sLocalInfiniteRestriction_normTwist (S := ∅) w s g
    by_cases hw : w.IsReal
    · have hshape : realShape[hw, (sLocalInfiniteRestriction w (emptyChart s)), s, (0 : Fin 2)] := by
        intro x
        have hn : ‖((realModel(hw)).symm (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
            (map_zero (realModel(hw)).symm) (x : ℝ)
        rw [hval]
        simp [InfinitePlace.mult, hw, hn]
      have h := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (emptyChart s))).unique
        (realLocalEulerParameters w hw _).exists.choose_spec (y₂ := (s, 0)) hshape
      simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, ↓reduceIte, h, Fin.val_zero,
        Nat.cast_zero, add_zero]
    · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have hshape : complexShape[hc, (sLocalInfiniteRestriction w (emptyChart s)), s, (0 : ℤ)] := by
        intro x
        have hn : ‖((complexModel(hc)).symm (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
            (map_zero (complexModel(hc)).symm) (x : ℂ)
        rw [hval]
        simp [InfinitePlace.mult, hw, hn]
      have h := (complexLocalEulerParameters w hc (sLocalInfiniteRestriction w (emptyChart s))).unique
        (complexLocalEulerParameters w hc _).exists.choose_spec (y₂ := (s, 0)) hshape
      simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, ↓reduceIte, h, Int.natAbs_zero,
        Nat.cast_zero, zero_div, add_zero]
  simp_rw [hfac]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  simp_rw [InfinitePlace.not_isReal_iff_isComplex]
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]

-- TODO(paper-gap): The description after (3.3.1.25) calls local insertion
-- injective. For ℚ with only its real place, insertion kills the diagonal unit −1.

/-- Paper: Remark 3.3.1.6, p. 135. The chosen unitary base lifts to a unitary
idele class character, and the finite set of places can be enlarged to kill
the Picard group.
Deviation: Agreement is expressed through the restriction in §3.1.2. The lift
is unramified outside S because its prescribed value on the outside unit
factors is trivial. -/
theorem sLocal_character_extension (χ : PontryaginDual Jₛ) :
    ∃ (χ' : PontryaginDual C𝔽) (h : ideleClassNormTwist χ' 0 ∈ unramifiedOutside F S),
      sIdeleRestriction F S ⟨ideleClassNormTwist χ' 0, h⟩ = chartₛ(χ) 0 ∧
      ∃ T : Finset Primes, S ⊆ T ∧ Subsingleton (CommRing.Pic ((T : Set Primes).integer F)) := by
  let ψ := (circleToComplex).comp χ
  obtain ⟨c, hc⟩ := sIdeleRestriction_surjective F S ψ
  have hn (x : C𝔽) : c.val x ≠ 0 := ((Group.isUnit x).map c.val).ne_zero
  let e : PontryaginDual C𝔽 :=
    { toFun x := ⟨c.val x / (‖c.val x‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
        rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr (hn x))])⟩
      map_one' := Subtype.ext (by simp)
      map_mul' x y := Subtype.ext (by
        change c.val (x * y) / (‖c.val (x * y)‖ : ℂ) =
          (c.val x / (‖c.val x‖ : ℂ)) * (c.val y / (‖c.val y‖ : ℂ))
        rw [map_mul, norm_mul, Complex.ofReal_mul, div_mul_div_comm])
      continuous_toFun := (c.val.continuous.div (Complex.continuous_ofReal.comp c.val.continuous.norm)
        (fun x ↦ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hn x)))).subtype_mk _ }
  have he (x : C𝔽) : ideleClassNormTwist e 0 x = c.val x / (‖c.val x‖ : ℂ) := by
    change (e x : ℂ) * (((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
    rfl
  have hu : ideleClassNormTwist e 0 ∈ unramifiedOutside F S := by
    apply (mem_unramifiedOutside_iff F S _).mpr
    intro v hv u
    let y := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
    let x := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v y
    have hx : c.val x = 1 := (mem_unramifiedOutside_iff F S c.val).mp c.property v hv u
    change ideleClassNormTwist e 0 x = 1
    simp [he, hx]
  refine ⟨e, hu, ?_, (picard_uniformization F S).1⟩
  ext1 x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  let y := QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F) (sIdeleInsertion F S g)
  have hval : c.val y = (χ (QuotientGroup.mk g) : ℂ) := by
    have h := DFunLike.congr_fun hc (QuotientGroup.mk g)
    rw [sIdeleRestriction_mk] at h
    exact h
  rw [sIdeleRestriction_mk]
  change ideleClassNormTwist e 0 y = (χ (QuotientGroup.mk g) : ℂ) * _ ^ (0 : ℂ)
  simp [he, hval]

local notation "sProdUnits" => ContinuousMulEquiv.prodUnits
  (InfiniteAdeleRing F) ((v : S) → v.val.adicCompletion F)
local notation "sInfiniteUnit(" w ", " x ")" => (sProdUnits).symm
  (ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) w x), 1)
local notation "sFiniteUnit(" v ", " x ")" => (sProdUnits).symm
  (1, ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x))

/-- Inserting an infinite local unit through the S-ideles gives its full idele insertion. -/
private theorem sIdeleInsertion_infiniteUnit (w : InfinitePlace F) (x : w.Completionˣ) :
    sIdeleInsertion F S (sInfiniteUnit(w, x)) = IdeleGroup.ofCompletion (𝓞 F) F w x := by
  classical
  obtain ⟨ha, hf, ho⟩ := sIdeleInsertion_apply F S (sInfiniteUnit(w, x))
  apply Units.ext
  apply Prod.ext
  · rw [ha]
    funext u
    change ((Pi.mulSingle (M := fun t ↦ t.Completionˣ) w x u : u.Completionˣ) : u.Completion) =
      Pi.mulSingle (M := fun t ↦ t.Completion) w (x : w.Completion) u
    by_cases hu : u = w
    · subst u
      simp
    · simp [Pi.mulSingle_eq_of_ne hu]
  · apply RestrictedProduct.ext
    intro v
    change (sIdeleInsertion F S (sInfiniteUnit(w, x))).val.2 v = 1
    by_cases hv : v ∈ S
    · exact hf ⟨v, hv⟩
    · exact ho v hv

/-- Inserting a finite local unit through the S-ideles gives its full idele insertion. -/
private theorem sIdeleInsertion_finiteUnit (v : S) (x : (v.val.adicCompletion F)ˣ) :
    sIdeleInsertion F S (sFiniteUnit(v, x)) = IdeleGroup.ofAdicCompletion (𝓞 F) F v.val x := by
  classical
  let : DecidableEq S := Classical.decEq _
  obtain ⟨ha, hf, ho⟩ := sIdeleInsertion_apply F S (sFiniteUnit(v, x))
  apply Units.ext
  apply Prod.ext
  · exact ha
  · apply RestrictedProduct.ext
    intro u
    change (sIdeleInsertion F S (sFiniteUnit(v, x))).val.2 u =
      RestrictedProduct.mulSingle (fun w : Primes ↦ w.adicCompletionIntegers F) v.val x.val u
    by_cases hu : u = v.val
    · subst u
      rw [hf v, RestrictedProduct.mulSingle_eq_same]
      change ((Pi.mulSingle (M := fun t : S ↦ (t.val.adicCompletion F)ˣ) v x v :
        (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F) = _
      rw [Pi.mulSingle_eq_same]
    · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hu]
      by_cases hm : u ∈ S
      · rw [hf ⟨u, hm⟩]
        change ((Pi.mulSingle (M := fun t : S ↦ (t.val.adicCompletion F)ˣ) v x ⟨u, hm⟩ :
          (u.adicCompletion F)ˣ) : u.adicCompletion F) = 1
        rw [Pi.mulSingle_eq_of_ne (fun e ↦ hu (congrArg Subtype.val e)), Units.val_one]
      · exact ho u hm

/-- The finite local Euler factor of a restricted global twist uses the same
ramification condition and uniformizer value as the global finite Euler factor. -/
private theorem finiteLocalEulerFactor_eq_finiteHeckeEulerFactor
    (χ' : PontryaginDual C𝔽) (v : Primes) (s : ℂ) :
    finiteLocalEulerFactor v (finitePlaceRestriction F v (ideleClassNormTwist χ' s)) =
      finiteHeckeEulerFactor χ' v s := by
  classical
  let c := finitePlaceRestriction F v (ideleClassNormTwist χ' s)
  let c₀ := finitePlaceRestriction F v (ideleClassNormTwist χ' 0)
  have htwist (x : (v.adicCompletion F)ˣ) :
      c x = c₀ x * (‖x.val‖ : ℂ) ^ s := by
    let g := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v x
    change (χ' g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ' g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) * _
    rw [Complex.cpow_zero, mul_one, ideleClassNorm_ofAdicCompletion]
    rfl
  have hrestrict (x : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist χ' 0).restrict v x.val = c₀ x := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  have hunram : unramified[v, c] ↔ (ideleClassNormTwist χ' 0).IsUnramifiedAt v := by
    rw [HeckeCharacter.isUnramifiedAt_iff]
    refine forall_congr' fun u ↦ ?_
    let x := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
    change c x = 1 ↔ (ideleClassNormTwist χ' 0).restrict v x.val = 1
    have hn : ‖x.val‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := x)).mp
          ⟨u.val.property, u.inv.property⟩)
    rw [htwist, hn, Complex.ofReal_one, Complex.one_cpow, mul_one, hrestrict]
  change finiteLocalEulerFactor v c = finiteHeckeEulerFactor χ' v s
  by_cases hv : (ideleClassNormTwist χ' 0).IsUnramifiedAt v
  · rw [finiteLocalEulerFactor, ite_eq_left (hunram.mpr hv), finiteHeckeEulerFactor, ite_eq_left hv]
    let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    let hπ := val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
    let π := Units.mk0 _ hπ.ne_zero
    change (1 - c π)⁻¹ = _
    have hn := norm_uniformizer_adicCompletion v π.val hπ
    rw [htwist, hv.localValue_eq π.val hπ, hrestrict, hn,
      Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) s,
      Complex.cpow_neg, Complex.ofReal_natCast]
  · rw [finiteLocalEulerFactor, ite_eq_right (mt hunram.mp hv), finiteHeckeEulerFactor,
      ite_eq_right hv]

/-- The product of local factors of the infinite restrictions of a global
norm twist is the global gamma factor. -/
private theorem prod_infiniteLocalEulerFactor_eq_heckeGammaFactor
    (χ' : PontryaginDual C𝔽) (s : ℂ) :
    (∏ w : InfinitePlace F,
      infiniteLocalEulerFactor w (infinitePlaceRestriction F w (ideleClassNormTwist χ' s))) =
      heckeGammaFactor χ' s := by
  classical
  unfold heckeGammaFactor
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  let c := infinitePlaceRestriction F w (ideleClassNormTwist χ' s)
  let c₀ := infinitePlaceRestriction F w (ideleClassNormTwist χ' 0)
  have htwist (x : w.Completionˣ) :
      c x = c₀ x * ((‖x.val‖ ^ w.mult : ℝ) : ℂ) ^ s := by
    let g := IdeleClassGroup.ofCompletion (𝓞 F) F w x
    change (χ' g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ' g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) * _
    rw [Complex.cpow_zero, mul_one, ideleClassNorm_ofCompletion]
    rfl
  change infiniteLocalEulerFactor w c = _
  by_cases hw : w.IsReal
  · let a := (realHeckeCharacter_parameters χ' w hw).exists.choose
    have ha := (realHeckeCharacter_parameters χ' w hw).exists.choose_spec.2
    have hshape : realShape[hw, c, s + a.1, a.2] := by
      intro x
      have hn : ‖((realModel(hw)).symm (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
          (map_zero (realModel(hw)).symm) (x : ℝ)
      have hx : (‖(x : ℝ)‖ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)
      rw [htwist, ha, Complex.cpow_add _ _ hx]
      change _ * ((‖((realModel(hw)).symm (x : ℝ) : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s = _
      simp only [hn, InfinitePlace.mult, hw, ite_true, pow_one]
      ac_rfl
    have hp := (realLocalEulerParameters w hw c).unique
      (realLocalEulerParameters w hw c).exists.choose_spec (y₂ := (s + a.1, a.2)) hshape
    simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hp, a]
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let a := (complexHeckeCharacter_parameters χ' w hc).exists.choose
    have ha := (complexHeckeCharacter_parameters χ' w hc).exists.choose_spec.2
    have hshape : complexShape[hc, c, s + a.1, a.2] := by
      intro x
      have hn : ‖((complexModel(hc)).symm (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
          (map_zero (complexModel(hc)).symm) (x : ℂ)
      have hx : ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero))
      rw [htwist, ha, Complex.cpow_add _ _ hx]
      change _ * ((‖((complexModel(hc)).symm (x : ℂ) : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s = _
      simp only [hn, InfinitePlace.mult, hw, ite_false]
      ac_rfl
    have hp := (complexLocalEulerParameters w hc c).unique
      (complexLocalEulerParameters w hc c).exists.choose_spec (y₂ := (s + a.1, a.2)) hshape
    simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hp, a]

/-- Paper: Remark 3.3.1.6, p. 135. Along the component of any such lift,
the S-local product matches the selected Euler factors of the global L-function. -/
theorem sLocalHeckeL_eq_partialEulerProduct (χ : PontryaginDual Jₛ) (χ' : PontryaginDual C𝔽)
    (h : ideleClassNormTwist χ' 0 ∈ unramifiedOutside F S)
    (hχ : sIdeleRestriction F S ⟨ideleClassNormTwist χ' 0, h⟩ = chartₛ(χ) 0) (s : ℂ) :
    sLocalHeckeL (chartₛ(χ) s) =
      heckeGammaFactor χ' s * ∏ v : S, finiteHeckeEulerFactor χ' v.val s := by
  classical
  have htwist (g : (SAdeleRing F S)ˣ) :
      chartₛ(χ) s (QuotientGroup.mk g) =
        ideleClassNormTwist χ' s (QuotientGroup.mk (sIdeleInsertion F S g)) := by
    have hbase := DFunLike.congr_fun hχ (QuotientGroup.mk g)
    rw [sIdeleRestriction_mk] at hbase
    change (χ' (QuotientGroup.mk (sIdeleInsertion F S g)) : ℂ) * _ ^ (0 : ℂ) =
      (χ (QuotientGroup.mk g) : ℂ) * _ ^ (0 : ℂ) at hbase
    simp only [Complex.cpow_zero, mul_one] at hbase
    change (χ (QuotientGroup.mk g) : ℂ) *
        (((mₛ (QuotientGroup.mk g) : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ' (QuotientGroup.mk (sIdeleInsertion F S g)) : ℂ) * _ ^ s
    rw [← hbase, sIdeleQuotientNorm_mk, ← ideleNorm_sIdeleInsertion]
    rfl
  have hinfinite (w : InfinitePlace F) : sLocalInfiniteRestriction w (chartₛ(χ) s) =
      infinitePlaceRestriction F w (ideleClassNormTwist χ' s) := by
    ext1 x
    change chartₛ(χ) s (QuotientGroup.mk (sInfiniteUnit(w, x))) =
      ideleClassNormTwist χ' s (QuotientGroup.mk (IdeleGroup.ofCompletion (𝓞 F) F w x))
    rw [htwist, sIdeleInsertion_infiniteUnit]
  have hfinite (v : S) : sLocalFiniteRestriction v (chartₛ(χ) s) =
      finitePlaceRestriction F v.val (ideleClassNormTwist χ' s) := by
    ext1 x
    change chartₛ(χ) s (QuotientGroup.mk (sFiniteUnit(v, x))) =
      ideleClassNormTwist χ' s (QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val x))
    rw [htwist, sIdeleInsertion_finiteUnit]
  simp_rw [sLocalHeckeL, hinfinite, hfinite, prod_infiniteLocalEulerFactor_eq_heckeGammaFactor,
    finiteLocalEulerFactor_eq_finiteHeckeEulerFactor]

section StripDecay

open scoped ContDiff SchwartzMap

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "classOf" => (QuotientGroup.mk : Iₛ → Jₛ)

local instance stripNormOneMeasurableSpace : MeasurableSpace J₁ := borel _
local notation "μJ₁" => sLocalNormOneQuotientMeasure F S
local instance stripNormOneIsHaarMeasure : Measure.IsHaarMeasure (μJ₁ : Measure J₁) :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

/-- The exponential homeomorphism from the real line to the positive units. -/
private def expUnit : ℝ ≃ₜ ℝ≥0ˣ :=
  Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
local notation "radialTheta(" τ "," ψ "," f ")" =>
  (fun x : ℝ ↦ sLocalHomogeneousAdelicTheta F S μJ₁ ψ f (classOf (τ (expUnit x))))

/-- Coercing the exponential unit to a real gives the ordinary exponential. -/
private theorem expUnit_val (x : ℝ) : ((expUnit x : ℝ≥0) : ℝ) = Real.exp x := rfl

/-- Addition of logarithmic coordinates corresponds to multiplication of units. -/
private theorem expUnit_add (x y : ℝ) : expUnit (x + y) = expUnit x * expUnit y :=
  Units.ext (NNReal.coe_inj.mp (Real.exp_add x y))

/-- The exponential of zero is the identity unit. -/
private theorem expUnit_zero : expUnit 0 = 1 :=
  Units.ext (NNReal.coe_inj.mp Real.exp_zero)

/-- In logarithmic coordinates the derivative of homogeneous theta is theta
applied to the differentiated test function. -/
private theorem radialTheta_hasDerivAt (τ : ℝ≥0ˣ →ₜ* Iₛ) (ψ : PontryaginDual J₁)
    (f : ℬ(Aₛ)) (x : ℝ) :
    HasDerivAt radialTheta(τ, ψ, f)
      (radialTheta(τ, ψ, (sAdeleDirectionalDeriv F S τ f)) x) x := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hExp : Tendsto expUnit (𝓝[≠] (0 : ℝ)) (𝓝[≠] (1 : ℝ≥0ˣ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨((expUnit).continuous.tendsto' 0 1 expUnit_zero).mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact fun h ↦ ht ((expUnit).injective (h.trans expUnit_zero.symm))
  let θ := radialTheta(τ, ψ, f)
  change Tendsto (fun t : ℝ ↦ t⁻¹ • (θ (x + t) - θ x)) _ _
  have hTheta : Tendsto (fun t : ℝ ↦ (θ (x + t) - θ x) / ((Real.exp t : ℂ) - 1))
      (𝓝[≠] 0) (𝓝 (radialTheta(τ, ψ, (sAdeleDirectionalDeriv F S τ f)) x)) := by
    apply ((sLocalHomogeneousAdelicTheta_directionalDeriv F S τ μJ₁ ψ f
      (τ (expUnit x))).comp hExp).congr
    intro t
    have hmul : τ (expUnit t) * τ (expUnit x) = τ (expUnit (x + t)) := by
      rw [expUnit_add, map_mul τ (expUnit x) (expUnit t), mul_comm]
    change (sLocalHomogeneousAdelicTheta F S μJ₁ ψ f (classOf (τ (expUnit t) * τ (expUnit x))) -
      θ x) / (((((expUnit t : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) - 1) = _
    exact congrArg₂ (· / ·)
      (congrArg (fun u : Iₛ ↦ sLocalHomogeneousAdelicTheta F S μJ₁ ψ f (classOf u) - θ x) hmul)
      (congrArg (fun a : ℝ ↦ (a : ℂ) - 1) (expUnit_val t))
  have hRatio : Tendsto (fun t : ℝ ↦ (t⁻¹ : ℝ) • ((Real.exp t : ℂ) - 1))
      (𝓝[≠] 0) (𝓝 1) := by
    simpa using (hasDerivAt_iff_tendsto_slope_zero.mp (Real.hasDerivAt_exp 0).ofReal_comp)
  have hprod := hRatio.mul hTheta
  rw [one_mul] at hprod
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin (s := ({0} : Set ℝ)ᶜ) (a := 0)] with t ht
  have ht' : t ≠ 0 := ht
  have hd : (Real.exp t : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (fun he ↦ ht' (Real.exp_injective (by rw [Real.exp_zero]; exact_mod_cast he)))
  rw [smul_mul_assoc, mul_div_left_comm, div_self hd, mul_one]

/-- Paper: Lemma 3.3.1.7(1), p. 136. Along a homomorphic section of the
S-idelic norm, homogeneous theta weighted by a complex exponential of positive
real part decays exponentially at both ends of the logarithmic axis.
The small-norm estimate uses a smaller positive weight and the large-norm
estimate uses an inverse norm power exceeding the given weight. -/
private theorem sLocalHomogeneousAdelicTheta_weighted_radial_bound (τ : ℝ≥0ˣ →ₜ* Iₛ)
    (hτ : RightInverse τ (sIdeleNorm F S)) (ψ : PontryaginDual J₁) (f : ℬ(Aₛ))
    (c : ℂ) (hc : 0 < c.re) :
    ∃ M δ : ℝ, 0 ≤ M ∧ 0 < δ ∧ ∀ x : ℝ,
      ‖Complex.exp (c * x) * radialTheta(τ, ψ, f) x‖ ≤ M * Real.exp (-δ * |x|) := by
  let δ := c.re / 2
  have hδ : 0 < δ := half_pos hc
  let N := ⌊c.re + δ⌋₊ + 1
  have hN : c.re + δ < (N : ℝ) := Nat.lt_succ_floor _
  have hB : Bornology.IsVonNBounded ℂ ({f} : Set ℬ(Aₛ)) := Bornology.isVonNBounded_singleton (𝕜 := ℂ) f
  refine (sLocalHomogeneousAdelicTheta_norm_pow_bounded_threshold_one
    F S δ hδ μJ₁ ψ {f} hB).elim fun A hsmall ↦ ?_
  refine (sLocalHomogeneousAdelicTheta_decay_bounded_threshold_one
    F S μJ₁ ψ {f} hB N).elim fun B hlarge ↦ ?_
  let θ := radialTheta(τ, ψ, f)
  let M := max (max A B) ‖θ 0‖
  have hAM : A ≤ M := (le_max_left A B).trans (le_max_left _ _)
  have hBM : B ≤ M := (le_max_right A B).trans (le_max_left _ _)
  refine ⟨M, δ, hsmall.1.le.trans hAM, hδ, fun x ↦ ?_⟩
  let r : ℝ := (sIdeleNorm F S (τ (expUnit x)) : ℝ≥0)
  have hm : r = Real.exp x := by
    exact (congrArg (fun u : ℝ≥0ˣ ↦ ((u : ℝ≥0) : ℝ)) (hτ (expUnit x))).trans (expUnit_val x)
  change ‖Complex.exp (c * x) * θ x‖ ≤ _
  rw [norm_mul, Complex.norm_exp, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := hsmall.2 f (mem_singleton _) (τ (expUnit x)) (hm.trans_lt (Real.exp_lt_one_iff.mpr hx))
    change ‖r ^ δ • θ x‖ ≤ A at h
    rw [hm, ← Real.exp_mul x δ, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    rw [abs_of_neg hx, neg_mul_neg]
    have he : c.re * x = δ * x + x * δ := by dsimp [δ]; ring
    rw [he, Real.exp_add, mul_assoc, mul_comm M]
    exact mul_le_mul_of_nonneg_left (h.trans hAM) (Real.exp_nonneg _)
  · simpa only [abs_zero, mul_zero, Real.exp_zero, one_mul, mul_one] using
      (le_max_right (max A B) ‖θ 0‖)
  · have h := hlarge.2 f (mem_singleton _) (τ (expUnit x)) ((Real.one_lt_exp_iff.mpr hx).trans_eq hm.symm)
    change ‖θ x‖ ≤ B * (r ^ N)⁻¹ at h
    rw [hm, ← Real.exp_nat_mul, ← Real.exp_neg] at h
    rw [abs_of_pos hx]
    calc
      _ ≤ Real.exp (c.re * x) * (B * Real.exp (-((N : ℝ) * x))) :=
        mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
      _ = B * Real.exp (c.re * x + -((N : ℝ) * x)) := by rw [Real.exp_add]; ring
      _ ≤ M * Real.exp (-δ * x) := by
        refine mul_le_mul hBM (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (hsmall.1.le.trans hAM)
        linarith only [mul_lt_mul_of_pos_right hN hx]

/-- Multiplying homogeneous theta in logarithmic coordinates by a positive
complex exponential gives a Schwartz function. -/
private theorem exists_schwartz_weighted_radialTheta (τ : ℝ≥0ˣ →ₜ* Iₛ)
    (hτ : RightInverse τ (sIdeleNorm F S)) (ψ : PontryaginDual J₁) (f : ℬ(Aₛ))
    (c : ℂ) (hc : 0 < c.re) :
    ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = Complex.exp (c * x) * radialTheta(τ, ψ, f) x := by
  let profile (v : ℬ(Aₛ)) (x : ℝ) := Complex.exp (c * x) * radialTheta(τ, ψ, v) x
  let D : ℬ(Aₛ) → ℬ(Aₛ) := fun v ↦ c • v + sAdeleDirectionalDeriv F S τ v
  have hd (v : ℬ(Aₛ)) (x : ℝ) : HasDerivAt (profile v) (profile (D v) x) x := by
    have he := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c).cexp
    let Θ : ℬ(Aₛ) →ₗ[ℂ] C(Jₛ, ℂ) := sLocalHomogeneousAdelicTheta F S μJ₁ ψ
    let u : Jₛ := classOf (τ (expUnit x))
    have hD : Θ (D v) u = c * Θ v u + Θ (sAdeleDirectionalDeriv F S τ v) u := by
      have h := congrArg (fun g : C(Jₛ, ℂ) ↦ g u)
        ((Θ.map_add (c • v) (sAdeleDirectionalDeriv F S τ v)).trans
          (congrArg (· + Θ (sAdeleDirectionalDeriv F S τ v)) (Θ.map_smul c v)))
      exact h
    apply (he.mul (radialTheta_hasDerivAt τ ψ v x)).congr_deriv
    change Complex.exp (c * x) * (c * (1 : ℂ)) * Θ v u +
      Complex.exp (c * x) * Θ (sAdeleDirectionalDeriv F S τ v) u =
      Complex.exp (c * x) * Θ (D v) u
    have hfactor (u a b : ℂ) : u * (c * 1) * a + u * b = u * (c * a + b) := by ring
    exact (hfactor _ _ _).trans (congrArg (Complex.exp (c * x) * ·) hD.symm)
  have hi (n : ℕ) : iteratedDeriv n (profile f) = profile (D^[n] f) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
      exact funext fun x ↦ (hd _ x).deriv
  have hs : ContDiff ℝ (∞ : ℕ∞ω) (profile f) := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro n _
    rw [hi]
    exact fun x ↦ (hd _ x).differentiableAt
  refine ⟨⟨profile f, hs, ?_⟩, fun x ↦ rfl⟩
  intro k n
  obtain ⟨M, δ, hM, hδ, hbound⟩ := sLocalHomogeneousAdelicTheta_weighted_radial_bound τ hτ ψ (D^[n] f) c hc
  -- The exponential bound absorbs each Schwartz seminorm's polynomial weight.
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x : ℝ, ‖x‖ ^ k * Real.exp (-δ * |x|) ≤ B := by
    let d := δ / (k + 1 : ℝ)
    have hd : 0 < d := by dsimp [d]; positivity
    refine ⟨d⁻¹ ^ k, fun x ↦ ?_⟩
    have hx : |x| ≤ d⁻¹ * Real.exp (d * |x|) := by
      rw [inv_mul_eq_div, le_div_iff₀ hd, mul_comm]
      linarith [Real.add_one_le_exp (d * |x|)]
    have he : (k : ℝ) * (d * |x|) ≤ δ * |x| := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      dsimp [d]
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      linarith
    rw [Real.norm_eq_abs]
    calc
      _ ≤ (d⁻¹ * Real.exp (d * |x|)) ^ k * Real.exp (-δ * |x|) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hx _) (Real.exp_nonneg _)
      _ = d⁻¹ ^ k * Real.exp ((k : ℝ) * (d * |x|) + -δ * |x|) := by
        rw [mul_pow, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ d⁻¹ ^ k * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith)) (by positivity)
      _ = _ := mul_one _
  refine ⟨M * B, fun x ↦ ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hi]
  calc
    _ ≤ ‖x‖ ^ k * (M * Real.exp (-δ * |x|)) :=
      mul_le_mul_of_nonneg_left (hbound x) (by positivity)
    _ = M * (‖x‖ ^ k * Real.exp (-δ * |x|)) := mul_left_comm _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB x) hM

/-- The radial integral in logarithmic coordinates is the Mellin transform
of the weighted theta profile, with the weight subtracted from the exponent. -/
private theorem radialMellin_eq_mellin (τ : ℝ≥0ˣ →ₜ* Iₛ)
    (hτ : RightInverse τ (sIdeleNorm F S)) (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ)
    (z : ℂ) (e : ℝ)
    (hχ : ∀ t : ℝ≥0ˣ, (χ (classOf (τ t)) : ℂ) = ((((t : ℝ≥0) : ℝ) : ℂ) ^ z))
    (g : ℝ → ℂ)
    (hg : ∀ x : ℝ, g x = Complex.exp (((e : ℂ) + z) * x) *
      radialTheta(τ, (χ.comp ⟨Subgroup.subtype J₁, continuous_subtype_val⟩), f) x)
    (s : ℂ) :
    sLocalRadialMellinIntegral τ f χ s = mellin (fun t ↦ g (Real.log t)) (s - e) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have hmeasure : positiveRealHaar = volume.map expUnit := by
    apply congrArg (fun h : ℝ → ℝ≥0ˣ ↦ volume.map h)
    funext x
    apply Units.ext
    apply NNReal.eq
    exact Real.coe_toNNReal _ (Real.exp_pos x).le
  let ψ : PontryaginDual J₁ := χ.comp ⟨Subgroup.subtype J₁, continuous_subtype_val⟩
  let Θ (t : ℝ≥0ˣ) := sLocalHomogeneousAdelicTheta F S μJ₁ ψ f (classOf (τ t))
  let c (t : ℝ≥0ˣ) := chartₛ(χ) s (classOf (τ t))
  change (∫ t, Θ t * c t ∂positiveRealHaar) = _
  have hchange : (∫ t, Θ t * c t ∂positiveRealHaar) =
      ∫ x : ℝ, Θ (expUnit x) * c (expUnit x) :=
    (congrArg (fun μ : Measure ℝ≥0ˣ ↦ ∫ t, Θ t * c t ∂μ) hmeasure).trans
      (expUnit.measurableEmbedding.integral_map _)
  rw [hchange, mellin_logProfile_eq]
  apply integral_congr_ae
  filter_upwards with x
  have hpow (w : ℂ) : (Real.exp x : ℂ) ^ w = Complex.exp ((x : ℂ) * w) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  have hchart : c (expUnit x) = Complex.exp ((x : ℂ) * z + (x : ℂ) * s) := by
    let unorm (t : ℝ≥0ˣ) : ℂ := (((t : ℝ≥0) : ℝ) : ℂ)
    have hu : unorm (expUnit x) = (Real.exp x : ℂ) :=
      congrArg Complex.ofReal (expUnit_val x)
    have hm : mₛ (classOf (τ (expUnit x))) = expUnit x := hτ (expUnit x)
    calc
      c (expUnit x) = (χ (classOf (τ (expUnit x))) : ℂ) *
          unorm (mₛ (classOf (τ (expUnit x)))) ^ s := rfl
      _ = unorm (expUnit x) ^ z * unorm (expUnit x) ^ s :=
        congrArg₂ (· * ·) (hχ (expUnit x)) (congrArg (fun t ↦ unorm t ^ s) hm)
      _ = _ := by rw [hu, hpow, hpow, Complex.exp_add]
  rw [hchart]
  have hx : g x = Complex.exp (((e : ℂ) + z) * x) * Θ (expUnit x) := hg x
  rw [hx, ← mul_assoc, ← Complex.exp_add, mul_comm (Θ (expUnit x))]
  congr 2
  ring

/-- The holomorphic S-local zeta function has rapid decay uniformly on
each closed strip in the positive half-plane. -/
private theorem sLocalIdelicZFunction_heightBound (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C > (0 : ℝ), ∀ᶠ y : ℝ in comap abs atTop, ∀ σ ∈ Icc a b,
      ‖sLocalIdelicZFunction f (chartₛ(χ) (vert(σ, y)))‖ ≤ C / |y| ^ N := by
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* Iₛ := ⟨p.comp (canonicalIdeleNormSection F),
    hp.comp (canonicalIdeleNormSection_continuous F)⟩
  have hτ : RightInverse τ (sIdeleNorm F S) := thetaSection_rightInverse F S
  let q : Iₛ →ₜ* Jₛ := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let ψ : PontryaginDual J₁ := χ.comp ⟨Subgroup.subtype J₁, continuous_subtype_val⟩
  obtain ⟨z, ⟨hz, hχ⟩, -⟩ :=
    existsUnique_unitaryComplexPower (((circleToComplex).comp χ).comp (q.comp τ))
      (fun t ↦ Circle.norm_coe (χ (q (τ t))))
  let e := a / 2
  have he : 0 < e := half_pos ha
  obtain ⟨g, hg⟩ := exists_schwartz_weighted_radialTheta τ hτ ψ f ((e : ℂ) + z)
    (by simpa [hz] using he)
  have hweight (σ : ℝ) (hσ : σ ∈ Icc (a - e) (b - e)) :
      ∃ h : 𝓢(ℝ, ℂ), ∀ x : ℝ, h x = (Real.exp (σ * x) : ℂ) * g x := by
    have hs : 0 < (((σ + e : ℝ) : ℂ) + z).re := by
      simp only [Complex.add_re, Complex.ofReal_re, hz, add_zero]
      linarith [hσ.1]
    obtain ⟨h, hh⟩ := exists_schwartz_weighted_radialTheta τ hτ ψ f _ hs
    refine ⟨h, fun x ↦ ?_⟩
    let θ := radialTheta(τ, ψ, f) x
    calc
      h x = Complex.exp ((((σ + e : ℝ) : ℂ) + z) * x) * θ := hh x
      _ = (Real.exp (σ * x) : ℂ) * (Complex.exp (((e : ℂ) + z) * x) * θ) := by
        rw [Complex.ofReal_exp, Complex.ofReal_mul, ← mul_assoc, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      _ = _ := congrArg ((Real.exp (σ * x) : ℂ) * ·) (hg x).symm
  obtain ⟨C, hC, hbound⟩ :=
    mellin_eventualHeightBound_of_weighted_schwartz g (a - e) (b - e) (by linarith) hweight N hN
  refine ⟨C, hC, hbound.mono (fun y hy σ hσ ↦ ?_)⟩
  have hs : vert(σ, y) ∈ rightHalf := by
    have hpos : 0 < σ := ha.trans_le hσ.1
    simpa [mem_preimage, mem_Ioi, Complex.mul_I_re] using hpos
  have hc : ∃ (χ' : PontryaginDual Jₛ) (s : ℂ), s ∈ rightHalf ∧
      chartₛ(χ) (vert(σ, y)) = chartₛ(χ') s := ⟨χ, _, hs, rfl⟩
  rw [sLocalIdelicZFunction_eq_integral f hc, ← sLocalThetaMellinIntegral_eq_zeta f hc,
    ← sLocalRadialMellinIntegral_eq_theta τ hτ f χ _ hs,
    radialMellin_eq_mellin τ hτ f χ z e hχ g hg]
  have hσ' : σ - e ∈ Icc (a - e) (b - e) :=
    ⟨sub_le_sub_right hσ.1 _, sub_le_sub_right hσ.2 _⟩
  have harg : vert(σ, y) - (e : ℂ) = vert((σ - e : ℝ), y) := by
    push_cast
    ring
  rw [harg]
  exact hy (σ - e) hσ'

/-- The S-local zeta function decays faster than each inverse power of height on closed positive strips. -/
alias sLocalIdelicZFunction_rapid_decay_on_positive_strip := sLocalIdelicZFunction_heightBound

/-- Paper: Lemma 3.3.1.7(1), p. 135. On every bounded strip in the positive
half-plane the zeta function is uniformly Schwartz in height. -/
theorem sLocalIdelicZFunction_schwartzOnStrip (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ k : ℕ, UniformlySchwartzOnStrip
      (iteratedDeriv k (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s))) a b := by
  let Z (s : ℂ) := sLocalIdelicZFunction f (chartₛ(χ) s)
  have hOpen : IsOpen rightHalf := isOpen_Ioi.preimage Complex.continuous_re
  have hZ : DifferentiableOn ℂ Z rightHalf := by
    refine (sLocalThetaMellinIntegral_analyticOn f χ).differentiableOn.congr ?_
    intro s hs
    have hc : ∃ (χ' : PontryaginDual Jₛ) (w : ℂ), w ∈ rightHalf ∧
        chartₛ(χ) s = chartₛ(χ') w := ⟨χ, s, hs, rfl⟩
    exact (sLocalIdelicZFunction_eq_integral f hc).trans
      (sLocalThetaMellinIntegral_eq_zeta f hc).symm
  intro k
  refine ⟨hab, ?_, fun ε hε _ N hN ↦ ?_⟩
  · intro s hs
    have hpos : s ∈ rightHalf := ha.trans hs.1
    rw [iteratedDeriv_eq_iterate]
    exact ((hZ.analyticAt (hOpen.mem_nhds hpos)).iterated_deriv k).differentiableAt.differentiableWithinAt
  · -- The circle stays inside the wider strip and changes the height by at most one.
    let r := min (ε / 2) 1
    have hr : 0 < r := lt_min (half_pos hε) zero_lt_one
    have hrε : r ≤ ε / 2 := min_le_left _ _
    have hr1 : r ≤ 1 := min_le_right _ _
    obtain ⟨C, hC, hdecay⟩ := sLocalIdelicZFunction_heightBound f χ a b ha hab N hN
    obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp hdecay)
    refine ⟨(k.factorial : ℝ) * (2 ^ N * C) / r ^ k, by positivity, ?_⟩
    have hlarge : ∀ᶠ y : ℝ in comap abs atTop, max (T + 1) 2 ≤ |y| :=
      tendsto_comap.eventually (eventually_ge_atTop _)
    filter_upwards [hlarge] with y hy σ hσ
    let s := vert(σ, y)
    have hre : s.re = σ := by simp [s]
    have him : s.im = y := by simp [s]
    have hsub (w : ℂ) (hw : w ∈ Metric.closedBall s r) : w.re ∈ Icc a b := by
      have h := (Complex.abs_re_le_norm (w - s)).trans (mem_closedBall_iff_norm.mp hw)
      rw [Complex.sub_re, hre, abs_le] at h
      exact ⟨by linarith [hσ.1, h.1], by linarith [hσ.2, h.2]⟩
    have hdiff := hZ.diffContOnCl_ball (c := s) (R := r)
      (fun w hw ↦ ha.trans_le (hsub w hw).1)
    have hsphere (w : ℂ) (hw : w ∈ Metric.sphere s r) : ‖Z w‖ ≤ 2 ^ N * C / |y| ^ N := by
      have h := (Complex.abs_im_le_norm (w - s)).trans (mem_sphere_iff_norm.mp hw).le
      rw [Complex.sub_im, him] at h
      have hyw : |y| ≤ |w.im| + 1 := by
        have htriangle := abs_sub_abs_le_abs_sub y w.im
        rw [abs_sub_comm] at htriangle
        linarith
      have hTy : T + 1 ≤ |y| := (le_max_left _ _).trans hy
      have hy2 : 2 ≤ |y| := (le_max_right _ _).trans hy
      have hT' : T ≤ |w.im| := by linarith
      have hyw' : |y| / 2 ≤ |w.im| := by linarith
      have hypos : 0 < |y| := by linarith
      have hbound := hT |w.im| hT' w.im rfl w.re (hsub w (Metric.sphere_subset_closedBall hw))
      rw [Complex.re_add_im] at hbound
      calc
        ‖Z w‖ ≤ C / |w.im| ^ N := hbound
        _ ≤ C / (|y| / 2) ^ N := div_le_div_of_nonneg_left hC.le (by positivity)
          (pow_le_pow_left₀ (by positivity) hyw' _)
        _ = 2 ^ N * C / |y| ^ N := by rw [div_pow, div_div_eq_mul_div, mul_comm C]
    calc
      _ ≤ (k.factorial : ℝ) * (2 ^ N * C / |y| ^ N) / r ^ k :=
        Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr hdiff hsphere
      _ = _ := by simp only [div_eq_mul_inv]; ring

end StripDecay

/-- Paper: Equation (3.3.1.26), p. 135. The normalized S-local zeta function
is the meromorphic quotient by the local Euler product.
Deviation: The quotient is put in normal form before evaluation, so that a
removable singularity takes its limiting value. -/
def sLocalNormalizedZFunction (f : ℬ(SAdeleRing F S)) (c : QuasiCharacter Jₛ) : ℂ :=
  toMeromorphicNFOn (fun s : ℂ ↦
    let c' := quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ c s
    sLocalIdelicZFunction f c' / sLocalHeckeL c') univ 0

section NormCharts

variable {G : Type*} [CommGroup G] [TopologicalSpace G] (m : G →* ℝ≥0ˣ) (hm : Continuous m)

local notation "unitChart(" χ ")" => quasiCharacterNormTwist m hm ((circleToComplex).comp χ)

/-- The complex parameter is additive under successive norm twists. -/
private theorem norm_chart_twist (χ : PontryaginDual G) (s t : ℂ) :
    quasiCharacterNormTwist m hm (unitChart(χ) s) t = unitChart(χ) (s + t) := by
  ext1 g
  let N : ℂ := (((m g : ℝ≥0) : ℝ) : ℂ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (m g).ne_zero)
  change (χ g : ℂ) * N ^ s * N ^ t = (χ g : ℂ) * N ^ (s + t)
  rw [Complex.cpow_add _ _ hN, mul_assoc]

/-- The dual chart has inverse unitary base and reflected complex parameter. -/
private theorem dual_norm_chart [IsTopologicalGroup G] (χ : PontryaginDual G) (s : ℂ) :
    dualQuasiCharacter m hm (unitChart(χ) s) = unitChart(χ⁻¹) (1 - s) := by
  ext1 u
  let N : ℂ := (((m u : ℝ≥0) : ℝ) : ℂ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (m u).ne_zero)
  change N * unitChart(χ) s u⁻¹ = (χ⁻¹ u : ℂ) * N ^ (1 - s)
  rw [map_inv]
  change N * ((χ u : ℂ) * N ^ s)⁻¹ = (χ u : ℂ)⁻¹ * N ^ (1 - s)
  rw [mul_inv_rev, Complex.cpow_sub 1 s hN, Complex.cpow_one, div_eq_mul_inv]
  ac_rfl

/-- Removing the real power prescribed by the abscissa leaves a unitary character. -/
private theorem exists_unitary_norm_chart [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (hp : IsProperMap m) (hne : ∃ g, m g ≠ 1) (c : QuasiCharacter G) :
    ∃ (χ : PontryaginDual G) (s : ℂ), c = unitChart(χ) s := by
  let a := quasiCharacterAbscissa m hp hne c
  let d := quasiCharacterNormTwist m hm c (-(a : ℂ))
  have hrad (g : G) : (((m g : ℝ≥0) : ℝ) : ℂ) ^ (a : ℂ) = (‖c g‖ : ℂ) := by
    rw [← Complex.ofReal_cpow (NNReal.coe_nonneg _) a,
      norm_quasiCharacter_eq_rpow_abscissa m hp hne]
  have hd (g : G) : d g = c g / (‖c g‖ : ℂ) := by
    change c g * _ ^ (-(a : ℂ)) = _
    rw [Complex.cpow_neg, hrad, div_eq_mul_inv]
  have hn (g : G) : ‖c g‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit g).map c).ne_zero
  let χ : PontryaginDual G :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (by
        rw [hd, norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (hn g)])⟩
      map_one' := Subtype.ext d.map_one
      map_mul' x y := Subtype.ext (d.map_mul x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨χ, (a : ℂ), ContinuousMonoidHom.ext fun g ↦ ?_⟩
  change c g = d g * (((m g : ℝ≥0) : ℝ) : ℂ) ^ (a : ℂ)
  rw [hd, hrad, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hn g))]

end NormCharts

/-- Twisting a point of the norm-twist chart moves along the chart. -/
private theorem sLocal_chart_twist (χ : PontryaginDual Jₛ) (s t : ℂ) :
    quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ (chartₛ(χ) s) t = chartₛ(χ) (s + t) :=
  norm_chart_twist mₛ hmₛ χ s t

/-- The reciprocal of the S-local Euler product is entire in the norm-twist chart. -/
private theorem differentiable_inv_sLocalHeckeL (χ : PontryaginDual Jₛ) :
    Differentiable ℂ (fun s ↦ (sLocalHeckeL (chartₛ(χ) s))⁻¹) := by
  classical
  obtain ⟨χ', h, hχ, -⟩ := sLocal_character_extension χ
  simp_rw [sLocalHeckeL_eq_partialEulerProduct χ χ' h hχ, mul_inv, ← Finset.prod_inv_distrib]
  refine (differentiable_inv_heckeGammaFactor χ').mul
    (Differentiable.fun_finsetProd fun v _ ↦ ?_)
  unfold finiteHeckeEulerFactor
  split_ifs
  · simp_rw [inv_inv]
    have hq : (q(v.val) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      ((Ideal.absNorm_eq_zero_iff).not.mpr v.val.ne_bot)
    exact (differentiable_const _).sub ((differentiable_const _).mul
      ((differentiable_neg).const_cpow (Or.inl hq)))
  · simp_rw [inv_one]
    exact differentiable_const _

/-- The reciprocal partial Euler product is differentiable along every unitary norm-twist chart. -/
alias sLocalHeckeL_inv_differentiable := differentiable_inv_sLocalHeckeL

/-- Paper: Equation (3.3.1.26), p. 135. In the positive half-plane the
normalized function is the convergent zeta integral divided by the Euler product. -/
theorem sLocalNormalizedZFunction_eq_div (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ)
    {s : ℂ} (hs : s ∈ rightHalf) :
    sLocalNormalizedZFunction f (chartₛ(χ) s) =
      sLocalIdelicZetaIntegral f (chartₛ(χ) s) / sLocalHeckeL (chartₛ(χ) s) := by
  let Z (z : ℂ) := sLocalIdelicZFunction f (chartₛ(χ) z)
  let L (z : ℂ) := (sLocalHeckeL (chartₛ(χ) z))⁻¹
  have hL : Differentiable ℂ L := differentiable_inv_sLocalHeckeL χ
  have hz (z : ℂ) (hz : z ∈ rightHalf) : Z z = sLocalIdelicZetaIntegral f (chartₛ(χ) z) :=
    sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz, rfl⟩
  have hZ : AnalyticAt ℂ Z s := by
    apply ((sLocalIdelicZetaIntegral_analyticOn f χ) s hs).congr
    filter_upwards [(isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hs] with z h
    exact (hz z h).symm
  let H (t : ℂ) := Z (s + t) * L (s + t)
  have hH : MeromorphicOn H univ := by
    intro t _
    exact (((sLocalIdelicZFunction_meromorphic f χ).meromorphicOn (s + t) trivial).mul
      (hL.analyticAt _).meromorphicAt).comp_analyticAt (g := fun t ↦ s + t) (by fun_prop)
  have hH₀ : AnalyticAt ℂ H 0 := by
    have h := hZ.mul (hL.analyticAt s)
    exact (show AnalyticAt ℂ (Z * L) (s + 0) by simpa using h).comp (by fun_prop)
  simp only [sLocalNormalizedZFunction, sLocal_chart_twist, div_eq_mul_inv]
  change toMeromorphicNFOn H univ 0 = _
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hH (mem_univ 0),
    toMeromorphicNFAt_eq_self.mpr hH₀.meromorphicNFAt]
  simp only [H, add_zero, hz s hs, L]

/-- Multiply the local archimedean bounds with the correct multiplicity for
each place. The remaining height loss is polynomial. -/
private theorem inv_sLocalHeckeL_strip_bound (χ : PontryaginDual Jₛ) (a b : ℝ) (ha : 0 < a) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖(sLocalHeckeL (chartₛ(χ) s))⁻¹‖ ≤
        C * ((1 + |s.im|) * Real.exp (Real.pi * |s.im| / 4)) ^ Module.finrank ℚ F := by
  classical
  obtain ⟨η, h, hχ, -⟩ := sLocal_character_extension χ
  let H (s : ℂ) := (1 + |s.im|) * Real.exp (Real.pi * |s.im| / 4)
  let P (v : InfinitePlace F) (s : ℂ) :=
    (if hv : v.IsReal then
      let p := (realHeckeCharacter_parameters η v hv).exists.choose
      Complex.Gammaℝ (s + p.1 + (p.2.val : ℂ))
    else
      let p := (complexHeckeCharacter_parameters η v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      Complex.Gammaℂ (s + p.1 + (p.2.natAbs : ℂ) / 2) / 2)⁻¹
  have hP (v : InfinitePlace F) : ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b → ‖P v s‖ ≤ C * H s ^ v.mult := by
    by_cases hv : v.IsReal
    · let p := (realHeckeCharacter_parameters η v hv).exists.choose
      have hp : p.1.re = 0 := (realHeckeCharacter_parameters η v hv).exists.choose_spec.1
      let w := p.1 + (p.2.val : ℂ)
      have hw : 0 ≤ w.re := by simp [w, hp]
      obtain ⟨C, hC, h⟩ := exists_norm_inv_GammaReal_add_le_on_strip a b ha w hw
      refine ⟨C, hC, fun s hs ↦ ?_⟩
      simpa only [P, dite_eq_left hv, hv.mult_eq_one, pow_one, add_assoc, H, w, p] using h s hs
    · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
      let p := (complexHeckeCharacter_parameters η v hc).exists.choose
      have hp : p.1.re = 0 := (complexHeckeCharacter_parameters η v hc).exists.choose_spec.1
      let w := p.1 + (p.2.natAbs : ℂ) / 2
      have hw : 0 ≤ w.re := by simp [w, hp]; positivity
      obtain ⟨C, hC, h₁⟩ := exists_norm_inv_GammaReal_add_le_on_strip a b ha w hw
      obtain ⟨D, hD, h₂⟩ := exists_norm_inv_GammaReal_add_le_on_strip a b ha (w + 1) (by simp; linarith)
      refine ⟨2 * C * D, by positivity, fun s hs ↦ ?_⟩
      have he : P v s = 2 * ((Complex.Gammaℝ (s + w))⁻¹ * (Complex.Gammaℝ (s + (w + 1)))⁻¹) := by
        simp only [P, dite_eq_right hv, p, w, ← add_assoc, div_eq_mul_inv, mul_inv_rev, inv_inv,
          ← Complex.Gammaℝ_mul_Gammaℝ_add_one]
        ring
      rw [he, norm_mul, norm_mul, Complex.norm_two, hc.mult_eq_two]
      calc
        _ ≤ 2 * ((C * H s) * (D * H s)) := by gcongr; exacts [h₁ s hs, h₂ s hs]
        _ = _ := by ring
  choose C hC hP using hP
  let V (v : S) : ℝ := 1 + ‖(ideleClassNormTwist η 0).localValue v.val‖
  have hV (s : ℂ) (hs : s.re ∈ Icc a b) (v : S) : ‖(finiteHeckeEulerFactor η v.val s)⁻¹‖ ≤ V v := by
    unfold finiteHeckeEulerFactor
    split_ifs
    · rw [inv_inv]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, norm_mul]
      have hq : 1 < (q(v.val) : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
      have hpow : ‖(q(v.val) : ℂ) ^ (-s)‖ ≤ 1 := by
        rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq)]
        exact Real.rpow_le_one_of_one_le_of_nonpos hq.le (by simp; linarith [hs.1])
      exact add_le_add_right (mul_le_of_le_one_right (norm_nonneg ((ideleClassNormTwist η 0).localValue v.val)) hpow) _
    · simp [V]
  refine ⟨(∏ v, C v) * ∏ v, V v, mul_pos (Finset.prod_pos fun v _ ↦ hC v)
    (Finset.prod_pos fun v _ ↦ by dsimp [V]; positivity), fun s hs ↦ ?_⟩
  rw [sLocalHeckeL_eq_partialEulerProduct χ η h hχ, mul_inv, norm_mul, ← Finset.prod_inv_distrib, norm_prod]
  have hΓ : ‖(heckeGammaFactor η s)⁻¹‖ ≤ (∏ v, C v) * H s ^ Module.finrank ℚ F := by
    change ‖(∏ v, _)⁻¹‖ ≤ _
    rw [← Finset.prod_inv_distrib, norm_prod]
    calc
      (∏ v, ‖P v s‖) ≤ ∏ v, C v * H s ^ v.mult :=
        Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ hP v s hs)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  exact (mul_le_mul hΓ (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ hV s hs v))
    (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) (mul_nonneg (Finset.prod_nonneg fun v _ ↦ (hC v).le) (pow_nonneg (by dsimp [H]; positivity) _))).trans_eq (by ring)


/-- Paper: Equation (3.3.1.27), p. 135. The normalized zeta function has the
given Stirling growth bound uniformly on each closed positive strip.
Deviation: The real exponential uses absolute height in both directions. -/
theorem sLocalNormalizedZFunction_heightBound (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (N : ℕ) (hN : 1 ≤ N) :
    let d : ℝ := (InfinitePlace.nrRealPlaces F : ℝ) / 2 + InfinitePlace.nrComplexPlaces F
    ∃ C > (0 : ℝ), ∀ᶠ t : ℝ in comap abs atTop, ∀ σ ∈ Icc a b,
      ‖sLocalNormalizedZFunction f (chartₛ(χ) (vert(σ, t)))‖ ≤
        C * |t| ^ (-((N : ℝ) + (σ - 1 / 2) * d)) * Real.exp (Real.pi * |t| / 2 * d) :=
  by
  classical
  let n := Module.finrank ℚ F
  let d := (InfinitePlace.nrRealPlaces F : ℝ) / 2 + InfinitePlace.nrComplexPlaces F
  obtain ⟨D, hD, hL⟩ := inv_sLocalHeckeL_strip_bound χ a b ha
  let M := n + ⌈(N : ℝ) + (b - 1 / 2) * d⌉₊ + N
  obtain ⟨C, hC, hZ⟩ := sLocalIdelicZFunction_heightBound f χ a (b + 1) ha (by linarith) M
    (by dsimp [M]; omega)
  refine ⟨C * D * 2 ^ n, by positivity, ?_⟩
  filter_upwards [hZ, (tendsto_comap (f := (abs : ℝ → ℝ))).eventually_ge_atTop 1] with t ht ht₁ σ hσ
  let z := vert(σ,t)
  have hre : z.re = σ := by simp [z]
  have him : z.im = t := by simp [z]
  have hpos : z ∈ rightHalf := by change 0 < z.re; rw [hre]; exact ha.trans_le hσ.1
  have hz := ht σ ⟨hσ.1, by linarith [hσ.2]⟩
  have hprod : ‖sLocalNormalizedZFunction f (chartₛ(χ) z)‖ =
      ‖sLocalIdelicZFunction f (chartₛ(χ) z)‖ * ‖(sLocalHeckeL (chartₛ(χ) z))⁻¹‖ := by
    rw [sLocalNormalizedZFunction_eq_div f χ hpos, ← sLocalIdelicZFunction_eq_integral f ⟨χ, z, hpos, rfl⟩,
      div_eq_mul_inv, norm_mul]
  have ht₀ : 0 < |t| := zero_lt_one.trans_le ht₁
  have hds : 0 ≤ d := by dsimp [d]; positivity
  have hn : (n : ℝ) / 2 = d := by
    dsimp [n, d]
    rw [← InfinitePlace.card_add_two_mul_card_eq_rank]
    push_cast
    ring
  have hbound : (n : ℝ) - M ≤ -((N : ℝ) + (σ - 1 / 2) * d) := by
    have hceil := Nat.le_ceil ((N : ℝ) + (b - 1 / 2) * d)
    dsimp [M]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right (sub_le_sub_right hσ.2 (1/2)) hds]
  have hp : |t| ^ n / |t| ^ M ≤ |t| ^ (-((N : ℝ) + (σ - 1 / 2) * d)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub ht₀]
    exact Real.rpow_le_rpow_of_exponent_le ht₁ hbound
  have he : Real.exp (Real.pi * |t| / 4) ^ n = Real.exp (Real.pi * |t| / 2 * d) := by
    rw [← Real.exp_nat_mul, ← hn]
    congr 1
    ring
  have hγ := hL z (hre.symm ▸ hσ)
  rw [him] at hγ
  rw [hprod]
  calc
    _ ≤ (C / |t| ^ M) * (D * ((1 + |t|) * Real.exp (Real.pi * |t| / 4)) ^ n) :=
      mul_le_mul hz hγ (norm_nonneg _) (by positivity)
    _ ≤ (C / |t| ^ M) * (D * ((2 * |t|) * Real.exp (Real.pi * |t| / 4)) ^ n) := by gcongr; linarith
    _ = (C * D * 2 ^ n) * (|t| ^ n / |t| ^ M) * Real.exp (Real.pi * |t| / 2 * d) := by
      rw [mul_pow, mul_pow, he]; ring
    _ ≤ _ := by gcongr

-- TODO(paper-gap): The proof's (3.3.1.34) inserts an extra ε_S in the
-- decomposition of Z_S/L_S. The estimate above uses the quotient in (3.3.1.26).
-- Footnote 2 asks for a reference for the uniform rapid decay of the finite-place quotient.

/-- Paper: Lemma 3.3.1.7(3)(a)(i)–(ii), p. 135. The infinite epsilon factor
depends on the real sign parity or the absolute complex angular weight.
Deviation: The phase is i to that power for the conjugate Fourier kernel
of App. A and D and the direction of Tate's equation used in §3.3.1. -/
def infiniteLocalEpsilonFactor (w : InfinitePlace F) (c : QuasiCharacter w.Completionˣ) : ℂ :=
  open Classical in
  if hw : w.IsReal then
    Complex.I ^ (realLocalEulerParameters w hw c).exists.choose.2.val
  else
    Complex.I ^ (complexLocalEulerParameters w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) c).exists.choose.2.natAbs

/-- Paper: Lemma 3.3.1.7(3)(a)(i), p. 135. The odd real component contributes
the constant epsilon factor i with the existing Fourier transform.
Deviation: The printed phase is conjugated. -/
theorem infiniteLocalEpsilonFactor_real_odd (w : InfinitePlace F) (hw : w.IsReal)
    (c : QuasiCharacter w.Completionˣ) (s : ℂ) (hc : realShape[hw, c, s, 1]) :
    infiniteLocalEpsilonFactor w c = Complex.I := by
  have h := (realLocalEulerParameters w hw c).unique
    (realLocalEulerParameters w hw c).exists.choose_spec (y₂ := (s, 1)) hc
  simp only [infiniteLocalEpsilonFactor, hw, ↓reduceDIte, h, Fin.val_one, pow_one]

/-- Paper: Lemma 3.3.1.7(3)(a)(iii), pp. 135–136. The finite epsilon factor
is the local Tate factor with the two local Euler factors removed.
Deviation: Normal form retains removable values. The Tate factor uses the
standard local character, with the finite-place sign fixed in App. A. -/
def finiteLocalEpsilonFactor (v : Primes) (c : QuasiCharacter (v.adicCompletion F)ˣ) : ℂ :=
  toMeromorphicNFOn (fun s : ℂ ↦
    let c' := quasiCharacterNormTwist m𝔭(v) h𝔭(v) c s
    finiteLocalTateFactor v c' / finiteLocalEulerFactor v c' *
      finiteLocalEulerFactor v (dualQuasiCharacter m𝔭(v) h𝔭(v) c')) univ 0

/-- Paper: Lemma 3.3.1.7(3)(a), p. 135. The infinite local epsilon factor
is entire in each norm-twist chart. -/
theorem infiniteLocalEpsilonFactor_entire (w : InfinitePlace F) (χ : PontryaginDual w.Completionˣ) :
    AnalyticOnNhd ℂ (infiniteLocalEpsilonFactor w ∘ chart∞[w, χ]) univ := by
  suffices h : ∀ s, infiniteLocalEpsilonFactor w (chart∞[w, χ] s) =
      infiniteLocalEpsilonFactor w (chart∞[w, χ] 0) by
    rw [show infiniteLocalEpsilonFactor w ∘ chart∞[w, χ] =
      fun _ ↦ infiniteLocalEpsilonFactor w (chart∞[w, χ] 0) from funext h]
    exact fun _ _ ↦ analyticAt_const
  intro s
  have hval (t : ℂ) (g : w.Completionˣ) : chart∞[w, χ] t g =
      (χ g : ℂ) * ((((m∞(w) g : ℝ≥0) : ℝ)) : ℂ) ^ t := rfl
  by_cases hw : w.IsReal
  · have hp := (realLocalEulerParameters w hw (chart∞[w, χ] 0)).exists.choose_spec
    have hshape : realShape[hw, (chart∞[w, χ] s),
        (realLocalEulerParameters w hw (chart∞[w, χ] 0)).exists.choose.1 + s,
        (realLocalEulerParameters w hw (chart∞[w, χ] 0)).exists.choose.2] := by
      intro x
      have hn : ‖((realModel(hw)).symm (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
          (map_zero (realModel(hw)).symm) (x : ℝ)
      have h0 := hp x
      rw [hval, Complex.cpow_zero, mul_one] at h0
      have hm : (((m∞(w) (Units.map (realModel(hw)).symm.toMonoidHom x) : ℝ≥0) : ℝ)) =
          ‖(x : ℝ)‖ := by
        simp [InfinitePlace.mult, hw, hn]
      have hx : ((‖(x : ℝ)‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)
      rw [hval, h0, hm, Complex.cpow_add _ _ hx]
      ring
    have h := (realLocalEulerParameters w hw (chart∞[w, χ] s)).unique
      (realLocalEulerParameters w hw (chart∞[w, χ] s)).exists.choose_spec
      (y₂ := ((realLocalEulerParameters w hw (chart∞[w, χ] 0)).exists.choose.1 + s,
        (realLocalEulerParameters w hw (chart∞[w, χ] 0)).exists.choose.2)) hshape
    simp only [infiniteLocalEpsilonFactor, hw, ↓reduceDIte, h]
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    have hp := (complexLocalEulerParameters w hc (chart∞[w, χ] 0)).exists.choose_spec
    have hshape : complexShape[hc, (chart∞[w, χ] s),
        (complexLocalEulerParameters w hc (chart∞[w, χ] 0)).exists.choose.1 + s,
        (complexLocalEulerParameters w hc (chart∞[w, χ] 0)).exists.choose.2] := by
      intro x
      have hn : ‖((complexModel(hc)).symm (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
          (map_zero (complexModel(hc)).symm) (x : ℂ)
      have h0 := hp x
      rw [hval, Complex.cpow_zero, mul_one] at h0
      have hm : (((m∞(w) (Units.map (complexModel(hc)).symm.toMonoidHom x) : ℝ≥0) : ℝ)) =
          ‖(x : ℂ)‖ ^ 2 := by
        simp [InfinitePlace.mult, hw, hn]
      have hx : (((‖(x : ℂ)‖ ^ 2 : ℝ)) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero))
      rw [hval, h0, hm, Complex.cpow_add _ _ hx]
      ring
    have h := (complexLocalEulerParameters w hc (chart∞[w, χ] s)).unique
      (complexLocalEulerParameters w hc (chart∞[w, χ] s)).exists.choose_spec
      (y₂ := ((complexLocalEulerParameters w hc (chart∞[w, χ] 0)).exists.choose.1 + s,
        (complexLocalEulerParameters w hc (chart∞[w, χ] 0)).exists.choose.2)) hshape
    simp only [infiniteLocalEpsilonFactor, hw, ↓reduceDIte, h]

/-- Paper: Equation (3.3.1.28), p. 135. The S-local epsilon factor is the
product of the epsilon factors of the restricted quasi-characters. -/
def sLocalEpsilonFactor (c : QuasiCharacter Jₛ) : ℂ :=
  (∏ w : InfinitePlace F, infiniteLocalEpsilonFactor w (sLocalInfiniteRestriction w c)) *
    ∏ v : S, finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v c)

/-- Paper: Equation (3.3.1.28), p. 135. With only archimedean places, the
trivial component has epsilon factor one. -/
theorem sLocalEpsilonFactor_archimedean_trivial (s : ℂ) :
    sLocalEpsilonFactor (emptyChart s) = 1 := by
  rw [sLocalEpsilonFactor, Finset.univ_eq_attach, Finset.attach_empty, Finset.prod_empty, mul_one]
  refine Finset.prod_eq_one fun w _ ↦ ?_
  have hval (g : w.Completionˣ) : sLocalInfiniteRestriction w (emptyChart s) g =
      (((m∞(w) g : ℝ≥0) : ℝ) : ℂ) ^ s :=
    sLocalInfiniteRestriction_normTwist (S := ∅) w s g
  by_cases hw : w.IsReal
  · have hshape : realShape[hw, (sLocalInfiniteRestriction w (emptyChart s)), s, (0 : Fin 2)] := by
      intro x
      have hn : ‖((realModel(hw)).symm (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
          (map_zero (realModel(hw)).symm) (x : ℝ)
      rw [hval]
      simp [InfinitePlace.mult, hw, hn]
    have h := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (emptyChart s))).unique
      (realLocalEulerParameters w hw _).exists.choose_spec (y₂ := (s, 0)) hshape
    simp only [infiniteLocalEpsilonFactor, hw, ↓reduceDIte, h, Fin.val_zero, pow_zero]
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    have hshape : complexShape[hc, (sLocalInfiniteRestriction w (emptyChart s)), s, (0 : ℤ)] := by
      intro x
      have hn : ‖((complexModel(hc)).symm (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
          (map_zero (complexModel(hc)).symm) (x : ℂ)
      rw [hval]
      simp [InfinitePlace.mult, hw, hn]
    have h := (complexLocalEulerParameters w hc (sLocalInfiniteRestriction w (emptyChart s))).unique
      (complexLocalEulerParameters w hc _).exists.choose_spec (y₂ := (s, 0)) hshape
    simp only [infiniteLocalEpsilonFactor, hw, ↓reduceDIte, h, Int.natAbs_zero, pow_zero]

section InfiniteTrace

open InfinitePlace.Completion
local notation "A(" k ")" => NumberField.AdeleRing (𝓞 k) k

/-- Projection and additive insertion at an archimedean place, in coordinates
on its real or complex model. -/
private def archEval {K : Type*} [Field K] (w : InfinitePlace F) (e : w.Completion ≃+* K) :
    A(F) →+* K :=
  e.toRingHom.comp ((Pi.evalRingHom _ w).comp (RingHom.fst _ _))

private def archSingle {K : Type*} [Field K] (w : InfinitePlace F) (e : w.Completion ≃+* K) :
    K →+ A(F) where
  toFun x := (@Pi.single _ _ (fun i ↦ inferInstanceAs (Zero i.Completion)) (Classical.decEq _) w (e.symm x), 0)
  map_zero' := by simp; rfl
  map_add' x y := Prod.ext (by simp [Pi.single_add]; rfl) (zero_add _).symm

private theorem archEval_single {K : Type*} [Field K] (w : InfinitePlace F)
    (e : w.Completion ≃+* K) (x : K) : archEval w e (archSingle w e x) = x := by
  classical
  change e (Pi.single w (e.symm x) w) = x
  rw [Pi.single_eq_same, e.apply_symm_apply]

private theorem archSingle_mul {K : Type*} [Field K] (w : InfinitePlace F)
    (e : w.Completion ≃+* K) (a : A(F)) (x : K) :
    archSingle w e (archEval w e a * x) = a * archSingle w e x := by
  classical
  refine Prod.ext ?_ (mul_zero _).symm
  funext j
  change Pi.single w (e.symm (e (a.1 w) * x)) j = a.1 j * Pi.single w (e.symm x) j
  by_cases hj : j = w
  · subst j; simp
  · simp [Pi.single_eq_of_ne hj]

/-- Compatibility of the archimedean coordinate with the adelic trace gives
the real trace character in either local model. -/
private theorem infiniteLocalCharacter_trace {K : Type*} [NormedField K] [NormedAlgebra ℝ K]
    (w : InfinitePlace F) (e : w.Completion ≃+* K) (he : Continuous e) (x : w.Completion) :
    ψ∞(w) x = Circle.exp (2 * Real.pi * Algebra.trace ℝ K (e x)) := by
  classical
  let j := ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let p := archEval Rat.infinitePlace j
  let r := archSingle Rat.infinitePlace j
  let q := archEval w e
  let i := archSingle w e
  let ι := rationalAdeleEmbedding F
  let : Algebra A(ℚ) A(F) := ι.toAlgebra
  have hp (x : ℝ) : p (r x) = x := archEval_single _ _ x
  have hq (a b : A(ℚ)) (h : p a = p b) : q (ι a) = q (ι b) := by
    apply sub_eq_zero.mp
    rw [← map_sub, ← map_sub]
    change e ((ι (a-b)).1 w) = 0
    rw [(rationalAdeleEmbedding_spec F).2.2.1]
    · exact map_zero _
    · rw [Subsingleton.elim (w.comap (algebraMap ℚ F)) Rat.infinitePlace]
      exact sub_eq_zero.mpr (j.injective h)
  have hcont : Continuous (fun t : ℝ ↦ q (ι (r t))) := by
    have hr : Continuous r := by
      change Continuous (fun x : ℝ ↦ ((@Pi.single _ _ _ (Classical.decEq _) Rat.infinitePlace (j.symm x), 0) : A(ℚ)))
      apply Continuous.prodMk _ continuous_const
      apply continuous_pi
      intro j'
      obtain rfl := Subsingleton.elim j' Rat.infinitePlace
      simp only [Pi.single_eq_same]
      exact (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.continuous
    exact he.comp (((continuous_apply w).comp continuous_fst).comp ((rationalAdeleEmbedding_spec F).1.comp hr))
  have hcompat : (fun t : ℝ ↦ q (ι (r t))) = algebraMap ℝ K := by
    apply (Rat.denseRange_cast (𝕜 := ℝ)).equalizer hcont (continuous_algebraMap ℝ K)
    funext t
    have heval : p (algebraMap ℚ A(ℚ) t) = (t : ℝ) := by
      change extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (algebraMap ℚ Rat.infinitePlace.Completion t) = _
      simp
    change q (ι (r (t : ℝ))) = _
    rw [hq _ (algebraMap ℚ A(ℚ) t) ((hp _).trans heval.symm), (rationalAdeleEmbedding_spec F).2.1]
    exact DFunLike.congr_fun (Subsingleton.elim
      (q.comp ((algebraMap F A(F)).comp (algebraMap ℚ F))) ((algebraMap ℝ K).comp (algebraMap ℚ ℝ))) t
  have hscalar (a : A(ℚ)) : q (algebraMap A(ℚ) A(F) a) = algebraMap ℝ K (p a) :=
    (hq a (r (p a)) (hp _).symm).trans (congrFun hcompat _)
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  obtain ⟨_, htr⟩ := trace_of_algebra_projection b p (fun t ↦ ⟨r t, hp t⟩) q i
    (archEval_single w e) hscalar (archSingle_mul w e)
  let y := e x
  let t := Algebra.trace A(ℚ) A(F) (i y)
  have hid : r 1 • i y = i y := by
    change algebraMap A(ℚ) A(F) (r 1) * i y = i y
    rw [← archSingle_mul, hscalar, hp, map_one, one_mul]
  have ht : r 1 * t = t := by
    change r 1 • Algebra.trace A(ℚ) A(F) (i y) = _
    rw [← map_smul, hid]
  have ht0 : t.2 = 0 := by
    have h := congrArg Prod.snd ht
    change 0 * t.2 = t.2 at h
    rwa [zero_mul, eq_comm] at h
  have hy : i y = (@Pi.single _ _ _ (Classical.decEq _) w x, 0) := by
    change (Pi.single w (e.symm (e x)), _) = _
    rw [e.symm_apply_apply]
  change ratAdeleStandardCharacter (Algebra.trace A(ℚ) A(F) _) = _
  rw [← hy]
  change ratAdeleStandardCharacter t = _
  rw [ratAdeleStandardCharacter_real t ht0]
  exact congrArg (fun a : ℝ ↦ Circle.exp (2 * Real.pi * a)) (htr y)

end InfiniteTrace

private theorem localSelfDual_map {R K : Type*} [NormedField R] [NormedField K]
    [MeasurableSpace R] [BorelSpace R] [MeasurableSpace K] [BorelSpace K]
    (k : R ≃+* K) (hk : Continuous k) (hki : Continuous k.symm)
    (ν₀ : Measure R) [hν₀ : ν₀.IsAddHaarMeasure] [ν₀.Regular] (ψ : R → Circle) (ψ' : K → Circle)
    (hψ : ∀ y, ψ' y = ψ (k.symm y)) (hdual : IsTamagawaSelfDual ν₀ ψ) :
    IsTamagawaSelfDual (ν₀.map k) ψ' := by
  let P := Multiplicative R
  let G := Multiplicative K
  let ν : Measure P := ν₀
  let u : P ≃ₜ* G :=
    { k.toAddEquiv.toMultiplicative with continuous_toFun := hk, continuous_invFun := hki }
  let μ : Measure G := ν.map u
  let : ν.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hν₀.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hν₀.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hν₀.map_add_left_eq_self x.toAdd }
  let : ν.Regular := inferInstanceAs ν₀.Regular
  let : MeasurableSpace (PontryaginDual P) := borel _
  let : BorelSpace (PontryaginDual P) := ⟨rfl⟩
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  have huμ : MeasurePreserving u ν μ := ⟨u.continuous.measurable, rfl⟩
  obtain ⟨d, hd, hν⟩ := hdual
  let u₁ : P →ₜ* G := ⟨u.toMulEquiv.toMonoidHom, u.continuous⟩
  let u₂ : G →ₜ* P := ⟨u.symm.toMulEquiv.toMonoidHom, u.symm.continuous⟩
  let t : PontryaginDual P ≃ₜ* PontryaginDual G :=
    { toFun := PontryaginDual.map u₂
      invFun := PontryaginDual.map u₁
      left_inv := fun χ ↦ PontryaginDual.ext fun x ↦ congrArg χ (u.symm_apply_apply x)
      right_inv := fun χ ↦ PontryaginDual.ext fun x ↦ congrArg χ (u.apply_symm_apply x)
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := (PontryaginDual.map u₂).continuous
      continuous_invFun := (PontryaginDual.map u₁).continuous }
  let e := u.symm.trans (d.trans t)
  refine ⟨e, fun x y ↦ ?_, ?_⟩
  · change d (Multiplicative.ofAdd (k.symm x)) (Multiplicative.ofAdd (k.symm y)) = _
    rw [hd, hψ, map_mul]
  let : μ.IsHaarMeasure := u.isHaarMeasure_map ν
  let : μ.Regular := Measure.Regular.map u.toHomeomorph
  change IsLCAPlancherelMeasure μ (μ.map e)
  change IsLCAPlancherelMeasure ν (ν.map d) at hν
  refine ⟨e.isHaarMeasure_map μ, Measure.Regular.map e.toHomeomorph, ?_⟩
  intro f hf₁ hf₂
  have hFourier : lcaFourier μ f ∘ t = lcaFourier ν (f ∘ u) := by
    funext χ
    let k : G → ℂ := fun x ↦ f x * star (t χ x : ℂ)
    change (∫ x, k x ∂μ) = _
    calc
      _ = ∫ x : P, k (u x) ∂ν :=
        (huμ.integral_comp u.toHomeomorph.measurableEmbedding k).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x ↦
        congrArg (fun z : P ↦ f (u x) * star (χ z : ℂ)) (u.symm_apply_apply x))
  have hmap : μ.map e = (ν.map d).map t := by
    have he : Measurable (e : G → PontryaginDual G) := e.continuous.measurable
    have ht : Measurable (t : PontryaginDual P → PontryaginDual G) := t.continuous.measurable
    have hd' : Measurable (d : P → PontryaginDual P) := d.continuous.measurable
    rw [← huμ.map_eq, Measure.map_map he huμ.measurable, Measure.map_map ht hd']
    congr 1
    funext x
    change t (d (u.symm (u x))) = t (d x)
    rw [u.symm_apply_apply]
  have h := hν.2.2 (f ∘ u) (huμ.integrable_comp_of_integrable hf₁)
    (hf₂.comp_measurePreserving huμ)
  have ht : MeasurableEmbedding (t : PontryaginDual P → PontryaginDual G) :=
    t.toHomeomorph.measurableEmbedding
  rw [hmap]
  refine ⟨ht.memLp_map_measure_iff.mpr (hFourier ▸ h.1), ?_⟩
  calc
    _ = eLpNorm (lcaFourier μ f ∘ t) 2 (ν.map d) := ht.eLpNorm_map_measure
    _ = eLpNorm (f ∘ u) 2 ν := hFourier.symm ▸ h.2
    _ = _ := eLpNorm_comp_measurePreserving hf₂.aestronglyMeasurable huμ

/-- Paper: Remark 3.3.1.8, p. 136. At each infinite place the additive
Tamagawa measure is self-dual for the restricted standard character. The finite
case is already stated as finiteLocalAdditiveTamagawaMeasure_selfDual. -/
theorem infiniteLocalAdditiveTamagawaMeasure_selfDual (w : InfinitePlace F) :
    IsTamagawaSelfDual (infiniteLocalAdditiveTamagawaMeasure F w) ψ∞(w) := by
  classical
  let : BorelSpace w.Completion := ⟨rfl⟩
  rw [infiniteLocalAdditiveTamagawaMeasure]
  split_ifs with hw
  · let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    apply localSelfDual_map (realModel(hw)).symm j.symm.continuous j.continuous _ _ _ _ realTamagawaMeasure_selfDual
    intro y
    exact (infiniteLocalCharacter_trace w (realModel(hw)) j.continuous y).trans (by simp)
  · let hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    have : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
      rw [← Nat.cast_smul_eq_nsmul ENNReal]
      norm_num only [Nat.cast_ofNat]
      exact Measure.IsAddHaarMeasure.smul _ (by norm_num) (by norm_num)
    have : (2 • (volume : Measure ℂ)).Regular := addHaar_regular_of_sigmaCompactSpace _
    apply localSelfDual_map (complexModel(hc)).symm j.symm.continuous j.continuous _ _ _ _ complexTamagawaMeasure_selfDual
    intro y
    refine (infiniteLocalCharacter_trace w (complexModel(hc)) j.continuous y).trans ?_
    rw [Algebra.trace_complex_apply]
    change Circle.exp (2 * Real.pi * (2 * _)) = Circle.exp (4 * Real.pi * ((complexModel(hc)) y).re)
    congr 1
    ring


/-! ## Local zeta functions and their poles -/

/-- Paper: Equation (3.3.2.1), p. 137. The archimedean zeta integral is
absolutely convergent on the positive half-plane. -/
theorem infiniteLocalIdelicZetaIntegral_integrable (w : InfinitePlace F) (f : ℬ(w.Completion))
    (χ : PontryaginDual w.Completionˣ) {s : ℂ} (hs : s ∈ rightHalf) :
    Integrable (fun g : w.Completionˣ ↦ test(f) g.val * chart∞[w, χ] s g) μ∞(w) := by
  let K := w.Completion
  have hσ : 0 < s.re := hs
  -- Measure the test function through the isometric embedding into the complex numbers.
  let ι := InfinitePlace.Completion.extensionEmbedding w
  have hι : Isometry ι := InfinitePlace.Completion.isometry_extensionEmbedding w
  have hιn (x : K) : ‖ι x‖ = ‖x‖ := hι.norm_map_of_map_zero (map_zero ι) x
  let m : Multiplicative K →* Multiplicative ℂ := ι.toAddMonoidHom.toMultiplicative
  have hm : Continuous m := continuous_ofAdd.comp (hι.continuous.comp continuous_toAdd)
  -- Compact subgroups of the completion are trivial, so every good subgroup is in the kernel.
  have hk (a : BruhatStructuralPair (Multiplicative K)) : OrderDual.ofDual a.val.2 ≤ m.ker := by
    let k := OrderDual.ofDual a.val.2
    have hkc := isCompact_lcaDualAnnihilator (lcaAnnihilator k) a.property.2.2.1.2.1
    rw [lcaDualAnnihilator_annihilator k a.property.2.2.1.1] at hkc
    obtain ⟨B, hB⟩ := hkc.exists_bound_of_continuousOn (continuous_toAdd.comp hm).continuousOn
    intro x hx
    rw [MonoidHom.mem_ker]
    by_contra h
    have hy : 0 < ‖(m x).toAdd‖ := norm_pos_iff.mpr (fun h0 ↦ h (toAdd_eq_zero.mp h0))
    obtain ⟨n, hn⟩ := exists_nat_gt (B / ‖(m x).toAdd‖)
    have hn' := hB (x ^ n) (k.pow_mem hx n)
    change ‖(m (x ^ n)).toAdd‖ ≤ B at hn'
    rw [map_pow, toAdd_pow, RCLike.norm_nsmul ℝ, nsmul_eq_mul] at hn'
    exact (not_lt_of_ge hn') ((div_lt_iff₀ hy).mp hn)
  obtain ⟨-, -, -, hdecay⟩ := schwartzBruhat_exists_coordinate_bounds
    (G := Multiplicative K) (T := PUnit.{1}) (fun _ ↦ PUnit.unit) (fun x ↦ ‖(m x).toAdd‖)
    (fun _ ↦ norm_nonneg _) (fun _ ↦ ⟨univ, isCompact_univ, fun _ _ ↦ mem_univ _⟩)
    (fun a e st N ↦ stage_exists_decay a e st N m hm (hk a)) f
  -- A power of the norm larger than the exponent controls the growth of the character.
  obtain ⟨k, hkσ⟩ := exists_nat_gt (2 * s.re)
  have hwk : (w.mult : ℝ) * s.re < k := by
    have hmult : (w.mult : ℝ) ≤ 2 := by
      by_cases h : w.IsReal
      · simp [h.mult_eq_one]
      · simp [(InfinitePlace.not_isReal_iff_isComplex.mp h).mult_eq_two]
    exact (mul_le_mul_of_nonneg_right hmult hσ.le).trans_lt hkσ
  obtain ⟨B₀, hB₀, hb₀⟩ := hdecay 0
  obtain ⟨B₁, hB₁, hb₁⟩ := hdecay k
  have hBd (x : K) : ‖f (Multiplicative.ofAdd x)‖ * (max 1 ‖x‖) ^ k ≤ max B₀ B₁ := by
    have hmx : ‖(m (Multiplicative.ofAdd x)).toAdd‖ = ‖x‖ := hιn x
    rcases le_total ‖x‖ 1 with hx | hx
    · have h := hb₀ (Multiplicative.ofAdd x)
      rw [pow_zero, mul_one] at h
      rw [max_eq_left hx, one_pow, mul_one]
      exact h.trans (le_max_left _ _)
    · have h := hb₁ (Multiplicative.ofAdd x)
      rw [hmx] at h
      rw [max_eq_right hx]
      exact h.trans (le_max_right _ _)
  have : BorelSpace K := ⟨rfl⟩
  have : BorelSpace Kˣ := borelSpace_units_of_continuousInv₀ K
  have ha := infiniteLocalTamagawa_integrable_norm_rpow w hσ k hwk
  refine (ha.2.const_mul (max B₀ B₁)).mono' ?_ (ae_of_all _ fun g ↦ ?_)
  · have hf : Continuous fun g : Kˣ ↦ f (Multiplicative.ofAdd g.val) :=
      (schwartzBruhat_continuous (G := Multiplicative K) f).comp
        (continuous_ofAdd.comp Units.continuous_val)
    exact (hf.mul (chart∞[w, χ] s).continuous).aestronglyMeasurable
  · have hchart : ‖chart∞[w, χ] s g‖ = ‖(g : K)‖ ^ ((w.mult : ℝ) * s.re) := by
      change ‖(χ g : ℂ) * ((((m∞(w) g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ s‖ = _
      rw [norm_mul, Circle.norm_coe, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
      have hval : (((m∞(w) g : ℝ≥0ˣ) : ℝ≥0) : ℝ) = ‖(g : K)‖ ^ w.mult := by
        simp [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
      rw [hval, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    rw [norm_mul, hchart]
    change ‖f (Multiplicative.ofAdd (g : K))‖ * ‖(g : K)‖ ^ ((w.mult : ℝ) * s.re) ≤
      max B₀ B₁ * (‖(g : K)‖ ^ ((w.mult : ℝ) * s.re) / (max 1 ‖(g : K)‖) ^ k)
    have hD : 0 < (max 1 ‖(g : K)‖) ^ k := by positivity
    rw [← mul_div_assoc, le_div_iff₀ hD, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (hBd _) (by positivity)

/-- Paper: Equation (3.3.2.1), p. 137. The finite local zeta integral is
absolutely convergent on the positive half-plane. -/
theorem finiteLocalIdelicZetaIntegral_integrable (v : Primes) (f : ℬ(v.adicCompletion F))
    (χ : PontryaginDual (v.adicCompletion F)ˣ) {s : ℂ} (hs : s ∈ rightHalf) :
    Integrable (fun g : (v.adicCompletion F)ˣ ↦ test(f) g.val * chart𝔭[v, χ] s g) μ𝔭(v) := by
  let K := v.adicCompletion F
  have : ProperSpace K := properSpace_adicCompletion v
  have hσ : 0 < s.re := hs
  -- The test function is bounded and vanishes off a compact set.
  have hstage (a : BruhatStructuralPair (Multiplicative K)) :
      ∃ C : Set K, IsCompact C ∧ ∀ x ∈ a.val.1, Multiplicative.toAdd x ∈ C := by
    obtain ⟨V, _, hV, hgen⟩ := a.property.2.1
    have hc : Continuous fun x : a.val.1 ↦ Multiplicative.toAdd (x : Multiplicative K) :=
      continuous_toAdd.comp continuous_subtype_val
    obtain ⟨r, hr⟩ := hV.exists_bound_of_continuousOn hc.continuousOn
    let ρ := max r 0
    let H : Subgroup (Multiplicative K) :=
      { carrier := {x | ‖Multiplicative.toAdd x‖ ≤ ρ}
        one_mem' := by simp [ρ]
        mul_mem' := fun hx hy ↦
          (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
        inv_mem' := fun {x} hx ↦ by
          change ‖Multiplicative.toAdd x⁻¹‖ ≤ ρ
          rw [toAdd_inv, norm_neg]
          exact hx }
    have hle : Subgroup.closure V ≤ H.comap a.val.1.subtype :=
      (Subgroup.closure_le _).2 fun x hx ↦ (hr x hx).trans (le_max_left _ _)
    rw [hgen] at hle
    refine ⟨Metric.closedBall 0 ρ, isCompact_closedBall _ _, fun x hx ↦ ?_⟩
    have h := Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_top (x := (⟨x, hx⟩ : a.val.1))))
    change ‖Multiplicative.toAdd x‖ ≤ ρ at h
    rwa [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨C, hC, hsupp, hbd⟩ := schwartzBruhat_exists_coordinate_bounds
    (G := Multiplicative K) (fun x ↦ Multiplicative.toAdd x)
    (fun x ↦ ‖((1 : Multiplicative K →* Multiplicative ℝ) x).toAdd‖) (fun _ ↦ norm_nonneg _)
    hstage (fun a e st N ↦ stage_exists_decay a e st N 1 continuous_const (by simp)) f
  obtain ⟨B, hB, hB'⟩ := hbd 0
  obtain ⟨R, hR⟩ := hC.exists_bound_of_continuousOn continuous_norm.continuousOn
  -- Dominate by a multiple of the truncated norm power.
  have : BorelSpace Kˣ := ⟨rfl⟩
  have hb := finiteLocalTamagawa_integrable_norm_rpow v hσ R
  refine (hb.2.const_mul B).mono' ?_ (ae_of_all _ fun g ↦ ?_)
  · have hf : Continuous fun g : Kˣ ↦ f (Multiplicative.ofAdd g.val) :=
      (schwartzBruhat_continuous (G := Multiplicative K) f).comp
        (continuous_ofAdd.comp Units.continuous_val)
    exact (hf.mul (chart𝔭[v, χ] s).continuous).aestronglyMeasurable
  · have hchart : ‖chart𝔭[v, χ] s g‖ = ‖(g : K)‖ ^ s.re := by
      change ‖(χ g : ℂ) * ((((m𝔭(v) g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ s‖ = _
      rw [norm_mul, Circle.norm_coe, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
      rfl
    rw [norm_mul, hchart]
    change ‖f (Multiplicative.ofAdd (g : K))‖ * ‖(g : K)‖ ^ s.re ≤ _
    by_cases hg : (g : K) ∈ C
    · have hRg : ‖(g : K)‖ ≤ R := by simpa using hR _ hg
      rw [indicator_of_mem (show g ∈ {u : Kˣ | ‖(u : K)‖ ≤ R} from hRg)]
      have h := hB' (Multiplicative.ofAdd (g : K))
      rw [pow_zero, mul_one] at h
      exact mul_le_mul_of_nonneg_right h (by positivity)
    · have h0 : f (Multiplicative.ofAdd (g : K)) = 0 := hsupp _ hg
      rw [h0, norm_zero, zero_mul]
      exact mul_nonneg hB (Set.indicator_nonneg (fun _ _ ↦ by positivity) _)

local notation "normBand[" m "," n "]" =>
  {g | (((m g : ℝ≥0) : ℝ)) ∈ Icc (n + 1 : ℝ)⁻¹ (n + 1)}

/-- Paper: Equation (3.3.2.1), p. 137. Norm-band truncations of the
archimedean zeta integral converge uniformly on compact positive exponent sets.
Deviation: Uniformity is stated on compact subsets of the convergence domain. -/
theorem infiniteLocalIdelicZetaIntegral_tendstoUniformlyOn (w : InfinitePlace F)
    (f : ℬ(w.Completion)) (χ : PontryaginDual w.Completionˣ) (K : Set ℂ)
    (hK : IsCompact K) (hKpos : K ⊆ rightHalf) :
    TendstoUniformlyOn (fun (n : ℕ) (s : ℂ) ↦
      ∫ g in normBand[m∞(w), n], test(f) g.val * chart∞[w, χ] s g ∂μ∞(w))
      (fun s ↦ localIdelicZetaIntegral μ∞(w) test(f) (chart∞[w, χ] s)) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hKne Complex.continuous_re.continuousOn
  let r (g : w.Completionˣ) : ℝ := (m∞(w) g : ℝ≥0)
  have hr (g : w.Completionˣ) : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hnorm (s : ℂ) (g : w.Completionˣ) : ‖chart∞[w, χ] s g‖ = r g ^ s.re := by
    change ‖(χ g : ℂ) * (r g : ℂ) ^ s‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hr g)]
  let integrand (s : ℂ) (g : w.Completionˣ) := test(f) g.val * chart∞[w, χ] s g
  have hint {s : ℂ} (hs : s ∈ K) : Integrable (integrand s) μ∞(w) :=
    infiniteLocalIdelicZetaIntegral_integrable w f χ (hKpos hs)
  -- The two endpoint characters bound the integrands below and above norm one.
  let bound (g : w.Completionˣ) := ‖integrand a g‖ + ‖integrand b g‖
  have hbound : Integrable bound μ∞(w) := (hint ha).norm.add (hint hb).norm
  have hle {c : ℂ} (hc : c ∈ K) (g : w.Completionˣ) : ‖integrand c g‖ ≤ bound g := by
    have hweighted {d : ℂ} (h : ‖chart∞[w, χ] c g‖ ≤ ‖chart∞[w, χ] d g‖) :
        ‖integrand c g‖ ≤ ‖integrand d g‖ := by
      dsimp only [integrand]
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    by_cases hg : r g ≤ 1
    · refine (hweighted (d := a) ?_).trans (le_add_of_nonneg_right (norm_nonneg (integrand b g)))
      rw [hnorm c, hnorm a]
      exact Real.rpow_le_rpow_of_exponent_ge (hr g) hg (hmin hc)
    · refine (hweighted (d := b) ?_).trans (le_add_of_nonneg_left (norm_nonneg (integrand a g)))
      rw [hnorm c, hnorm b]
      exact Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hg) (hmax hc)
  let B (n : ℕ) : Set w.Completionˣ := normBand[m∞(w), n]
  have hB (n : ℕ) : MeasurableSet (B n) := by
    let : BorelSpace w.Completion := ⟨rfl⟩
    let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
    have hcont : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp h∞(w))
    exact hcont.measurable measurableSet_Icc
  have hBmono : Monotone B := by
    intro i j hij g hg
    have hij' : (i : ℝ) + 1 ≤ j + 1 := by exact_mod_cast Nat.succ_le_succ hij
    exact ⟨((inv_le_inv₀ (by positivity) (by positivity)).mpr hij').trans hg.1,
      hg.2.trans hij'⟩
  have htail : (⋂ n, (B n)ᶜ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    obtain ⟨n, hn⟩ := exists_nat_gt (max (r g) (r g)⁻¹)
    have hn' : max (r g) (r g)⁻¹ ≤ (n : ℝ) + 1 :=
      hn.le.trans (le_add_of_nonneg_right zero_le_one)
    have hmem : g ∈ B n :=
      ⟨(inv_le_comm₀ (by positivity) (hr g)).2 ((le_max_right _ _).trans hn'),
        (le_max_left _ _).trans hn'⟩
    exact (mem_iInter.mp hg n) hmem
  have hlim : Tendsto (fun n ↦ ∫ g in (B n)ᶜ, bound g ∂μ∞(w)) atTop (𝓝 0) := by
    simpa only [htail, setIntegral_empty] using
      (tendsto_setIntegral_of_antitone (μ := μ∞(w)) (f := bound) (fun n ↦ (hB n).compl)
        (fun _ _ hij ↦ compl_subset_compl.mpr (hBmono hij)) ⟨0, hbound.integrableOn⟩)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with n hn c hc
  change dist (∫ g, integrand c g ∂μ∞(w)) (∫ g in B n, integrand c g ∂μ∞(w)) < ε
  rw [dist_eq_norm, ← integral_add_compl (hB n) (hint hc), add_sub_cancel_left]
  calc
    ‖∫ g in (B n)ᶜ, integrand c g ∂μ∞(w)‖ ≤ ∫ g in (B n)ᶜ, ‖integrand c g‖ ∂μ∞(w) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ g in (B n)ᶜ, bound g ∂μ∞(w) :=
      setIntegral_mono_on (hint hc).norm.integrableOn hbound.integrableOn (hB n).compl
        (fun g _ ↦ hle hc g)
    _ < ε := hn

/-- Paper: Equation (3.3.2.1), p. 137. Norm-band truncations of the
finite local zeta integral converge uniformly on compact positive exponent sets.
Deviation: Uniformity is stated on compact subsets of the convergence domain. -/
theorem finiteLocalIdelicZetaIntegral_tendstoUniformlyOn (v : Primes)
    (f : ℬ(v.adicCompletion F)) (χ : PontryaginDual (v.adicCompletion F)ˣ) (K : Set ℂ)
    (hK : IsCompact K) (hKpos : K ⊆ rightHalf) :
    TendstoUniformlyOn (fun (n : ℕ) (s : ℂ) ↦
      ∫ g in normBand[m𝔭(v), n], test(f) g.val * chart𝔭[v, χ] s g ∂μ𝔭(v))
      (fun s ↦ localIdelicZetaIntegral μ𝔭(v) test(f) (chart𝔭[v, χ] s)) atTop K := by
  let L := v.adicCompletion F
  have : ProperSpace L := properSpace_adicCompletion v
  have : BorelSpace Lˣ := ⟨rfl⟩
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  -- The real parts of the exponents lie in a compact interval of positive numbers.
  obtain ⟨s₁, hs₁, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨s₂, -, hmax⟩ := hK.exists_isMaxOn hne Complex.continuous_re.continuousOn
  let a := s₁.re
  let b := s₂.re
  have ha : 0 < a := hKpos hs₁
  have hb : 0 < b := ha.trans_le (hmax hs₁)
  -- The test function is bounded and vanishes outside a ball.
  have hstage (p : BruhatStructuralPair (Multiplicative L)) :
      ∃ C : Set L, IsCompact C ∧ ∀ x ∈ p.val.1, Multiplicative.toAdd x ∈ C := by
    obtain ⟨V, _, hV, hgen⟩ := p.property.2.1
    have hc : Continuous fun x : p.val.1 ↦ Multiplicative.toAdd (x : Multiplicative L) :=
      continuous_toAdd.comp continuous_subtype_val
    obtain ⟨r, hr⟩ := hV.exists_bound_of_continuousOn hc.continuousOn
    let ρ := max r 0
    let H : Subgroup (Multiplicative L) :=
      { carrier := {x | ‖Multiplicative.toAdd x‖ ≤ ρ}
        one_mem' := by simp [ρ]
        mul_mem' := fun hx hy ↦
          (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
        inv_mem' := fun {x} hx ↦ by
          change ‖Multiplicative.toAdd x⁻¹‖ ≤ ρ
          rw [toAdd_inv, norm_neg]
          exact hx }
    have hle : Subgroup.closure V ≤ H.comap p.val.1.subtype :=
      (Subgroup.closure_le _).2 fun x hx ↦ (hr x hx).trans (le_max_left _ _)
    rw [hgen] at hle
    refine ⟨Metric.closedBall 0 ρ, isCompact_closedBall _ _, fun x hx ↦ ?_⟩
    have h := Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_top (x := (⟨x, hx⟩ : p.val.1))))
    change ‖Multiplicative.toAdd x‖ ≤ ρ at h
    rwa [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨C, hC, hsupp, hbd⟩ := schwartzBruhat_exists_coordinate_bounds
    (G := Multiplicative L) (fun x ↦ Multiplicative.toAdd x)
    (fun x ↦ ‖((1 : Multiplicative L →* Multiplicative ℝ) x).toAdd‖) (fun _ ↦ norm_nonneg _)
    hstage (fun p e st N ↦ stage_exists_decay p e st N 1 continuous_const (by simp)) f
  obtain ⟨B, hB, hB'⟩ := hbd 0
  obtain ⟨R, hR⟩ := hC.exists_bound_of_continuousOn continuous_norm.continuousOn
  -- A majorant that works for every exponent in the compact set.
  let ind (σ : ℝ) := {u : Lˣ | ‖(u : L)‖ ≤ R}.indicator (fun u ↦ ‖(u : L)‖ ^ σ)
  let M : Lˣ → ℝ := fun u ↦ B * (ind a u + ind b u)
  have hM : Integrable M μ𝔭(v) :=
    ((finiteLocalTamagawa_integrable_norm_rpow v ha R).2.add
      (finiteLocalTamagawa_integrable_norm_rpow v hb R).2).const_mul B
  have hchart (s : ℂ) (g : Lˣ) : ‖chart𝔭[v, χ] s g‖ = ‖(g : L)‖ ^ s.re := by
    change ‖(χ g : ℂ) * ((((m𝔭(v) g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ s‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
    rfl
  have hdom (s : ℂ) (hs : s ∈ K) (g : Lˣ) :
      ‖test(f) g.val * chart𝔭[v, χ] s g‖ ≤ M g := by
    rw [norm_mul, hchart]
    change ‖f (Multiplicative.ofAdd (g : L))‖ * ‖(g : L)‖ ^ s.re ≤ M g
    by_cases hg : (g : L) ∈ C
    · have hRg : ‖(g : L)‖ ≤ R := by simpa using hR _ hg
      have hmem : g ∈ {u : Lˣ | ‖(u : L)‖ ≤ R} := hRg
      have hpos : 0 < ‖(g : L)‖ := norm_pos_iff.mpr g.ne_zero
      have hpow : ‖(g : L)‖ ^ s.re ≤ ind a g + ind b g := by
        simp only [ind, indicator_of_mem hmem]
        rcases le_total ‖(g : L)‖ 1 with h1 | h1
        · exact (Real.rpow_le_rpow_of_exponent_ge hpos h1 (hmin hs)).trans
            (le_add_of_nonneg_right (by positivity))
        · exact (Real.rpow_le_rpow_of_exponent_le h1 (hmax hs)).trans
            (le_add_of_nonneg_left (by positivity))
      have h := hB' (Multiplicative.ofAdd (g : L))
      rw [pow_zero, mul_one] at h
      exact mul_le_mul h hpow (by positivity) hB
    · have h0 : f (Multiplicative.ofAdd (g : L)) = 0 := hsupp _ hg
      rw [h0, norm_zero, zero_mul]
      exact mul_nonneg hB (add_nonneg (Set.indicator_nonneg (fun _ _ ↦ by positivity) _)
        (Set.indicator_nonneg (fun _ _ ↦ by positivity) _))
  -- The bands are measurable, increase, and exhaust the units.
  let band (n : ℕ) : Set Lˣ := normBand[m𝔭(v), n]
  have hcont : Continuous fun g : Lˣ ↦ (((m𝔭(v) g : ℝ≥0ˣ) : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (continuous_finiteLocalModule v))
  have hbandm (n : ℕ) : MeasurableSet (band n) := hcont.measurable measurableSet_Icc
  have hmono : Monotone band := by
    intro n k hnk g hg
    have h : (n + 1 : ℝ) ≤ k + 1 := by exact_mod_cast Nat.succ_le_succ hnk
    exact ⟨(inv_anti₀ (by positivity) h).trans hg.1, hg.2.trans h⟩
  have hunion : (⋃ n, band n) = univ := by
    refine eq_univ_of_forall fun g ↦ mem_iUnion.mpr ?_
    have hpos : 0 < (((m𝔭(v) g : ℝ≥0ˣ) : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    obtain ⟨n, hn⟩ := exists_nat_ge (max (((m𝔭(v) g : ℝ≥0ˣ) : ℝ≥0) : ℝ)
      ((((m𝔭(v) g : ℝ≥0ˣ) : ℝ≥0) : ℝ))⁻¹)
    refine ⟨n, ?_, ?_⟩
    · rw [inv_le_comm₀ (by positivity) hpos]
      exact (le_max_right _ _).trans (hn.trans (by linarith))
    · exact (le_max_left _ _).trans (hn.trans (by linarith))
  -- The tails of the majorant tend to zero.
  have htail : Tendsto (fun n ↦ ∫ g in (band n)ᶜ, M g ∂μ𝔭(v)) atTop (𝓝 0) := by
    have h := tendsto_setIntegral_of_monotone (μ := μ𝔭(v)) hbandm hmono
      (by rw [hunion]; exact hM.integrableOn)
    rw [hunion, Measure.restrict_univ] at h
    have heq (n : ℕ) : ∫ g in (band n)ᶜ, M g ∂μ𝔭(v) =
        ∫ g, M g ∂μ𝔭(v) - ∫ g in band n, M g ∂μ𝔭(v) := by
      rw [← integral_add_compl (hbandm n) hM, add_sub_cancel_left]
    simp_rw [heq]
    simpa using (tendsto_const_nhds (x := ∫ g, M g ∂μ𝔭(v))).sub h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.1 htail).2 ε hε] with n hn s hs
  have hint := finiteLocalIdelicZetaIntegral_integrable v f χ (hKpos hs)
  rw [dist_eq_norm, localIdelicZetaIntegral, ← integral_add_compl (hbandm n) hint,
    add_sub_cancel_left]
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le hM.integrableOn
    (ae_of_all _ fun g ↦ hdom s hs g)) hn

section FourierTest

variable {K : Type*} [NormedField K] [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K] [SigmaCompactSpace K]

/-- A self-dual character identifies the Schwartz–Bruhat Fourier transform on the dual
with a test function on the field itself. -/
private theorem exists_localSchwartzFourierMap (ν : Measure K) [hν : ν.IsAddHaarMeasure]
    (ψ : K → Circle) (hψ : IsTamagawaSelfDual ν ψ) :
    ∃ T : ℬ(K) →L[ℂ] ℬ(K), ∀ f, test(T f) = tamagawaFourier ν ψ test(f) := by
  let G := Multiplicative K
  let μ : Measure G := ν
  let : LocallyCompactSpace G := ‹LocallyCompactSpace K›
  let : BorelSpace G := ‹BorelSpace K›
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hν.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hν.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hν.map_add_left_eq_self x.toAdd }
  let : μ.Regular := addHaar_regular_of_sigmaCompactSpace ν
  refine hψ.elim fun e he ↦ ?_
  refine (schwartzBruhat_fourier_equiv μ).elim fun T hT ↦ ?_
  refine (exists_schwartzBruhat_comp_equivCLM e).elim fun P hP ↦ ?_
  refine ⟨P.comp T.toContinuousLinearMap, fun f ↦ funext fun y ↦ ?_⟩
  calc
    P (T f) (Multiplicative.ofAdd y) = T f (e (Multiplicative.ofAdd y)) := hP _ _
    _ = lcaFourier μ f (e (Multiplicative.ofAdd y)) := (hT f).2 _
    _ = _ := (tamagawaFourier_eq_lcaFourier ν ψ test(f) y (e (Multiplicative.ofAdd y)) (fun x ↦ by
      rw [mul_comm x y]
      exact he.1 y x)).symm


private theorem exists_localSchwartzFourier (ν : Measure K) [hν : ν.IsAddHaarMeasure]
    (ψ : K → Circle) (hψ : IsTamagawaSelfDual ν ψ) (f : ℬ(K)) :
    ∃ g : ℬ(K), test(g) = tamagawaFourier ν ψ test(f) := by
  refine (exists_localSchwartzFourierMap ν ψ hψ).elim fun T hT ↦ ?_
  exact ⟨T f, hT f⟩

end FourierTest

section LocalAnalytic

variable {K : Type*} [NormedField K] [MeasurableSpace Kˣ] [BorelSpace Kˣ]

local notation "twist(" m "," hm "," χ ")" =>
  quasiCharacterNormTwist m hm ((circleToComplex).comp χ)

/-- Absolute convergence at the endpoints of a slightly larger strip controls
the derivative under the local integral. -/
private theorem localIdelicZetaIntegral_analyticAt (m : Kˣ →* ℝ≥0ˣ) (hm : Continuous m)
    (μ : Measure Kˣ) (f : K → ℂ) (χ : PontryaginDual Kˣ) (p : ℝ)
    (hint : ∀ z : ℂ, p < z.re → Integrable (fun g : Kˣ ↦ f g.val * twist(m, hm, χ) z g) μ) :
    AnalyticOnNhd ℂ (fun z ↦ localIdelicZetaIntegral μ f (twist(m, hm, χ) z)) (Complex.re ⁻¹' Ioi p) := by
  let r (g : Kˣ) : ℝ := (m g : ℝ≥0)
  have hr (g : Kˣ) : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hrc : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp hm)
  let A (z : ℂ) (g : Kˣ) := f g.val * twist(m, hm, χ) z g
  let A' (z : ℂ) (g : Kˣ) := A z g * (Real.log (r g) : ℂ)
  have hderiv (g : Kˣ) (z : ℂ) : HasDerivAt (A · g) (A' z g) z := by
    have h := ((Complex.hasStrictDerivAt_const_cpow (x := (r g : ℂ)) (y := z)
      (Or.inl (Complex.ofReal_ne_zero.mpr (hr g).ne'))).hasDerivAt.const_mul
      (χ g : ℂ)).const_mul (f g.val)
    change HasDerivAt (fun t ↦ f g.val * ((χ g : ℂ) * (r g : ℂ) ^ t))
      ((f g.val * ((χ g : ℂ) * (r g : ℂ) ^ z)) * (Real.log (r g) : ℂ)) z
    simpa only [← Complex.ofReal_log (hr g).le, mul_assoc] using h
  have hnorm (g : Kˣ) (z : ℂ) :
      ‖A z g‖ = ‖f g.val‖ * Real.exp (Real.log (r g) * z.re) := by
    change ‖f g.val * ((χ g : ℂ) * (r g : ℂ) ^ z)‖ = _
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hr g),
      Real.rpow_def_of_pos (hr g)]
  intro s hs
  apply DifferentiableOn.analyticAt (s := Complex.re ⁻¹' Ioi p) _ ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hs)
  intro z hz
  have hpos : p < z.re := hz
  let δ := (z.re - p) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let a : ℂ := (z.re - 2 * δ : ℝ)
  let b : ℂ := (z.re + 2 * δ : ℝ)
  have ha : p < a.re := by dsimp [a, δ]; linarith
  have hb : p < b.re := by dsimp [b, δ]; linarith
  let V := Complex.re ⁻¹' Ioo (z.re - δ) (z.re + δ)
  have hV : V ∈ 𝓝 z := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
    ⟨by linarith, by linarith⟩
  let B (g : Kˣ) := δ⁻¹ * (‖A a g‖ + ‖A b g‖)
  have hB : Integrable B μ := ((hint a ha).norm.add (hint b hb).norm).const_mul _
  have hle (g : Kˣ) (w : ℂ) (hw : w ∈ V) : ‖A' w g‖ ≤ B g := by
    obtain ⟨hw₁, hw₂⟩ := hw
    let x := Real.log (r g)
    have hx : |x| ≤ δ⁻¹ * Real.exp (δ * |x|) := by
      rw [inv_mul_eq_div, le_div_iff₀ hδ, mul_comm]
      linarith only [Real.add_one_le_exp (δ * |x|)]
    change ‖A w g * (x : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ ‖A w g‖ * (δ⁻¹ * Real.exp (δ * |x|)) := by gcongr
      _ = δ⁻¹ * (‖f g.val‖ * Real.exp (x * w.re + δ * |x|)) := by
        rw [hnorm, Real.exp_add]; ring
      _ ≤ B g := by
        dsimp only [B]
        rw [hnorm, hnorm, ← mul_add]
        gcongr δ⁻¹ * (‖f g.val‖ * ?_)
        rcases le_total x 0 with hx | hx
        · apply le_add_of_le_of_nonneg _ (Real.exp_nonneg _)
          apply Real.exp_le_exp.mpr
          rw [abs_of_nonpos hx]
          change x * w.re + δ * -x ≤ x * (z.re - 2 * δ)
          nlinarith only [mul_nonpos_of_nonpos_of_nonneg hx (sub_nonneg.mpr hw₁.le)]
        · apply le_add_of_nonneg_of_le (Real.exp_nonneg _) _
          apply Real.exp_le_exp.mpr
          rw [abs_of_nonneg hx]
          change x * w.re + δ * x ≤ x * (z.re + 2 * δ)
          nlinarith only [mul_nonneg hx (sub_nonneg.mpr hw₂.le)]
  apply DifferentiableAt.differentiableWithinAt
  apply HasDerivAt.differentiableAt
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := A) (F' := A') hV
    ?_ (hint z hpos) ?_ (ae_of_all _ hle) hB (ae_of_all _ fun g w _ ↦ hderiv g w)).2
  · filter_upwards [(isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hz] with w hw
    exact (hint w hw).aestronglyMeasurable
  · exact (hint z hpos).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp (hrc.log (fun g ↦ (hr g).ne'))).aestronglyMeasurable

end LocalAnalytic

/-- Scalar meromorphic functions on the plane agreeing on a punctured germ
agree off a discrete set. -/
private theorem meromorphic_eq_of_germ {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g)
    {z : ℂ} (h : f =ᶠ[𝓝[≠] z] g) : f =ᶠ[codiscrete ℂ] g := by
  have hd : Meromorphic (f - g) := fun t ↦ (hf t).sub (hg t)
  have he := hd.exists_meromorphicOrderAt_eq_top_iff_eventually_zero.mp
    ⟨z, meromorphicOrderAt_eq_top_iff.mpr (h.mono fun _ ht ↦ sub_eq_zero.mpr ht)⟩
  exact he.mono fun _ ht ↦ sub_eq_zero.mp ht

section LocalContinuation

variable {K : Type*} [NormedField K] [MeasurableSpace Kˣ]

local notation "twist(" m "," hm "," χ ")" =>
  quasiCharacterNormTwist m hm ((circleToComplex).comp χ)

/-- Normalizing a germ after moving its center to the origin gives the value
of the global meromorphic normal form at the original center. -/
private theorem normalize_translate_at_zero {H : ℂ → ℂ} (hH : MeromorphicOn H univ) (s : ℂ) :
    toMeromorphicNFAt (fun t ↦ H (s + t)) 0 0 = toMeromorphicNFOn H univ s := by
  let G := toMeromorphicNFOn H univ
  have hG : MeromorphicNFAt G (s + 0) := meromorphicNFOn_toMeromorphicNFOn H univ (mem_univ _)
  have hT : Tendsto (fun t : ℂ ↦ s + t) (𝓝[≠] 0) (𝓝[≠] s) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using ((continuous_const_add s).tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  have hnear : (fun t ↦ H (s + t)) =ᶠ[𝓝[≠] 0] (fun t ↦ G (s + t)) :=
    hT.eventually (hH.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)).symm
  have hn : MeromorphicNFAt (fun t ↦ G (s + t)) 0 :=
    hG.comp_analyticAt (g := fun t ↦ s + t) (by fun_prop)
  rw [(toMeromorphicNFAt_eventuallyEq_nhds_congr hnear).eq_of_nhds,
    toMeromorphicNFAt_eq_self.mpr hn]
  change G (s + 0) = G s
  rw [add_zero]

/-- Glue the defining integral and its reflected Tate expression on their overlap.
Normalizing in the germ of a twist makes the construction independent of a
choice of unitary chart, including on the finite-place cylinder. -/
private theorem localIdelicZFunction_continuation
    (m : Kˣ →* ℝ≥0ˣ) (hm : Continuous m) (μ : Measure Kˣ) (T : (K → ℂ) → K → ℂ)
    (ρ : QuasiCharacter Kˣ → ℂ) (hρ : IsLocalTateFactor m hm μ T ρ)
    (a : QuasiCharacter Kˣ → ℝ) (ha : ∀ χ s, a (twist(m, hm, χ) s) = s.re)
    (hcover : ∀ c, ∃ χ s, c = twist(m, hm, χ) s)
    (f g : ℬ(K)) (hg : test(g) = T test(f))
    (hI : ∀ (u : ℬ(K)) χ, AnalyticOnNhd ℂ
      (fun s ↦ localIdelicZetaIntegral μ test(u) (twist(m, hm, χ) s)) rightHalf) :
    ∃! Z : QuasiCharacter Kˣ → ℂ, ∀ χ : PontryaginDual Kˣ,
      MeromorphicNFOn (Z ∘ twist(m, hm, χ)) univ ∧ EqOn (Z ∘ twist(m, hm, χ))
        (fun s ↦ localIdelicZetaIntegral μ test(f) (twist(m, hm, χ) s)) rightHalf := by
  classical
  let I (u : ℬ(K)) := localIdelicZetaIntegral μ test(u)
  let dual := dualQuasiCharacter m hm
  let H (c : QuasiCharacter Kˣ) := if 0 < a c then I f c else ρ c * I g (dual c)
  have hright (χ) {s : ℂ} (hs : 0 < s.re) :
      H (twist(m, hm, χ) s) = I f (twist(m, hm, χ) s) := ite_eq_left ((ha χ s).symm ▸ hs)
  have hleft (χ) {s : ℂ} (hs : s.re < 1) :
      H (twist(m, hm, χ) s) = ρ (twist(m, hm, χ) s) * I g (twist(m, hm, (χ⁻¹)) (1 - s)) := by
    rw [← dual_norm_chart m hm χ s]
    by_cases hp : 0 < s.re
    · rw [hright χ hp]
      simpa only [I, hg] using hρ.2 f χ s ⟨hp, hs⟩
    · exact ite_eq_right ((ha χ s).symm ▸ hp)
  have hR (χ) {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ (H ∘ twist(m, hm, χ)) s := by
    apply (hI f χ s hs).congr
    filter_upwards [(isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hs] with z hz
    exact (hright χ hz).symm
  have hM (χ) : MeromorphicOn (H ∘ twist(m, hm, χ)) univ := by
    intro s _
    by_cases hs : 0 < s.re
    · exact (hR χ hs).meromorphicAt
    · have hlt : s.re < 1 := (le_of_not_gt hs).trans_lt zero_lt_one
      have hpos : 1 - s ∈ rightHalf := by change 0 < (1 - s).re; simpa using sub_pos.mpr hlt
      have hmer := ((hρ.1 χ).meromorphicOn s trivial).mul
        (((hI g χ⁻¹ (1 - s) hpos).comp (f := fun z : ℂ ↦ 1 - z) (by fun_prop)).meromorphicAt)
      apply hmer.congr
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        ((isOpen_Iio.preimage Complex.continuous_re).mem_nhds hlt)] with z hz
      exact (hleft χ hz).symm
  let Z (c : QuasiCharacter Kˣ) := toMeromorphicNFAt (fun t ↦ H (quasiCharacterNormTwist m hm c t)) 0 0
  have hchart (χ) : Z ∘ twist(m, hm, χ) = toMeromorphicNFOn (H ∘ twist(m, hm, χ)) univ := by
    funext s
    change toMeromorphicNFAt (fun t ↦ H (quasiCharacterNormTwist m hm (twist(m, hm, χ) s) t)) 0 0 = _
    rw [show (fun t ↦ H (quasiCharacterNormTwist m hm (twist(m, hm, χ) s) t)) =
      (fun t ↦ (H ∘ twist(m, hm, χ)) (s + t)) from
        funext fun t ↦ congrArg H (norm_chart_twist m hm χ s t)]
    exact normalize_translate_at_zero (hM χ) s
  have hZ (χ) : MeromorphicNFOn (Z ∘ twist(m, hm, χ)) univ ∧ EqOn (Z ∘ twist(m, hm, χ))
      (fun s ↦ I f (twist(m, hm, χ) s)) rightHalf := by
    rw [hchart]
    refine ⟨meromorphicNFOn_toMeromorphicNFOn _ _, fun s hs ↦ ?_⟩
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (hM χ) trivial,
      toMeromorphicNFAt_eq_self.mpr (hR χ hs).meromorphicNFAt]
    exact hright χ hs
  refine ⟨Z, hZ, fun Y hY ↦ funext fun c ↦ ?_⟩
  obtain ⟨χ, s, rfl⟩ := hcover c
  let Yχ := Y ∘ twist(m, hm, χ)
  let Zχ := Z ∘ twist(m, hm, χ)
  have heq : Yχ =ᶠ[codiscrete ℂ] Zχ := by
    apply meromorphic_eq_of_germ (fun z ↦ (hY χ).1.meromorphicOn z trivial)
      (fun z ↦ (hZ χ).1.meromorphicOn z trivial) (z := 1)
    have h₁ : (1 : ℂ) ∈ rightHalf := by norm_num [mem_preimage, mem_Ioi]
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds h₁)] with z hz
    exact ((hY χ).2 hz).trans ((hZ χ).2 hz).symm
  change Yχ s = Zχ s
  apply EventuallyEq.eq_of_nhds (f := Yχ) (g := Zχ)
  apply (((hY χ).1 (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds ((hZ χ).1 (mem_univ s))).mp
  exact heq.filter_mono (nhdsNE_le_codiscrete s)

end LocalContinuation

/-- Paper: §3.3.2, p. 137. The archimedean integral (3.3.2.1) has a unique
meromorphic continuation, in normal form in every norm-twist chart. -/
theorem infiniteLocalIdelicZFunction_existsUnique (w : InfinitePlace F) (f : ℬ(w.Completion)) :
    ∃! Z : QuasiCharacter w.Completionˣ → ℂ, ∀ χ : PontryaginDual w.Completionˣ,
      MeromorphicNFOn (Z ∘ chart∞[w, χ]) univ ∧
        EqOn (Z ∘ chart∞[w, χ]) (fun s ↦ localIdelicZetaIntegral μ∞(w) test(f) (chart∞[w, χ] s))
          rightHalf := by
  have htwo : 1 < ‖(2 : w.Completion)‖ := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) (2 : w.Completion), map_ofNat]
    norm_num
  let : NontriviallyNormedField w.Completion := ⟨⟨2, htwo⟩⟩
  let : ProperSpace w.Completion :=
    .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace w.Completion
  let : LocallyCompactSpace w.Completionˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).locallyCompactSpace
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  have hp : IsProperMap m∞(w) := isProperMap_units_nnNorm_pow w.mult w.mult_ne_zero
  have hne : ∃ u, m∞(w) u ≠ 1 := by
    let u := Units.mk0 (2 : w.Completion) (by rintro h; rw [h, norm_zero] at htwo; linarith)
    refine ⟨u, fun he ↦ ?_⟩
    have hv := congrArg (fun y : ℝ≥0ˣ ↦ ((y : ℝ≥0) : ℝ)) he
    exact (one_lt_pow₀ htwo w.mult_ne_zero).ne' hv
  obtain ⟨g, hg⟩ := exists_localSchwartzFourier _ _ (infiniteLocalAdditiveTamagawaMeasure_selfDual w) f
  exact localIdelicZFunction_continuation _ _ _ _ _ (infiniteLocalTateFactor_spec w)
    (quasiCharacterAbscissa _ hp hne)
    (fun χ s ↦ quasiCharacterAbscissa_of_unitary_twist _ hp hne _ χ s (fun _ ↦ rfl))
    (exists_unitary_norm_chart _ _ hp hne) f g hg fun u χ ↦
      localIdelicZetaIntegral_analyticAt _ _ _ _ χ 0 fun _ hz ↦
        infiniteLocalIdelicZetaIntegral_integrable w u χ hz

/-- Paper: §3.3.2, p. 137. The archimedean Z-function is the meromorphic
continuation of the local integral. -/
def infiniteLocalIdelicZFunction (w : InfinitePlace F) (f : ℬ(w.Completion)) :
    QuasiCharacter w.Completionˣ → ℂ :=
  (infiniteLocalIdelicZFunction_existsUnique w f).exists.choose

/-- Paper: Equation (3.3.2.1), p. 137. In the half-plane of convergence the
archimedean Z-function gives the integral using the multiplicative Tamagawa measure. -/
theorem infiniteLocalIdelicZFunction_eq_integral (w : InfinitePlace F) (f : ℬ(w.Completion))
    (χ : PontryaginDual w.Completionˣ) {s : ℂ} (hs : s ∈ rightHalf) :
    infiniteLocalIdelicZFunction w f (chart∞[w, χ] s) =
      localIdelicZetaIntegral μ∞(w) test(f) (chart∞[w, χ] s) :=
  ((infiniteLocalIdelicZFunction_existsUnique w f).exists.choose_spec χ).2 hs

/-- Paper: §3.3.2, p. 137. The finite local integral (3.3.2.1) has a unique
meromorphic continuation, in normal form in every norm-twist chart. -/
theorem finiteLocalIdelicZFunction_existsUnique (v : Primes) (f : ℬ(v.adicCompletion F)) :
    ∃! Z : QuasiCharacter (v.adicCompletion F)ˣ → ℂ, ∀ χ : PontryaginDual (v.adicCompletion F)ˣ,
      MeromorphicNFOn (Z ∘ chart𝔭[v, χ]) univ ∧
        EqOn (Z ∘ chart𝔭[v, χ]) (fun s ↦ localIdelicZetaIntegral μ𝔭(v) test(f) (chart𝔭[v, χ] s))
          rightHalf := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : LocallyCompactSpace (v.adicCompletion F)ˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).locallyCompactSpace
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let : (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hp : IsProperMap m𝔭(v) := by
    simpa only [pow_one] using (isProperMap_units_nnNorm_pow (K := v.adicCompletion F) 1 one_ne_zero)
  have hne : ∃ u, m𝔭(v) u ≠ 1 := by
    let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
    let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
    refine ⟨u, fun he ↦ hπ.val_lt_one.ne ?_⟩
    apply Valued.toNormedField.norm_eq_one_iff.mp
    exact congrArg (fun t : ℝ≥0ˣ ↦ ((t : ℝ≥0) : ℝ)) he
  obtain ⟨g, hg⟩ := exists_localSchwartzFourier _ _ (finiteLocalAdditiveTamagawaMeasure_selfDual F v) f
  exact localIdelicZFunction_continuation _ _ _ _ _ (finiteLocalTateFactor_spec v)
    (quasiCharacterAbscissa _ hp hne)
    (fun χ s ↦ quasiCharacterAbscissa_of_unitary_twist _ hp hne _ χ s (fun _ ↦ rfl))
    (exists_unitary_norm_chart _ _ hp hne) f g hg fun u χ ↦
      localIdelicZetaIntegral_analyticAt _ _ _ _ χ 0 fun _ hz ↦
        finiteLocalIdelicZetaIntegral_integrable v u χ hz

/-- Paper: §3.3.2, p. 137. The finite local Z-function is the meromorphic
continuation of the local integral. -/
def finiteLocalIdelicZFunction (v : Primes) (f : ℬ(v.adicCompletion F)) :
    QuasiCharacter (v.adicCompletion F)ˣ → ℂ :=
  (finiteLocalIdelicZFunction_existsUnique v f).exists.choose

/-- Paper: Equation (3.3.2.1), p. 137. In the half-plane of convergence the
finite local Z-function gives the integral using the multiplicative Tamagawa measure. -/
theorem finiteLocalIdelicZFunction_eq_integral (v : Primes) (f : ℬ(v.adicCompletion F))
    (χ : PontryaginDual (v.adicCompletion F)ˣ) {s : ℂ} (hs : s ∈ rightHalf) :
    finiteLocalIdelicZFunction v f (chart𝔭[v, χ] s) =
      localIdelicZetaIntegral μ𝔭(v) test(f) (chart𝔭[v, χ] s) :=
  ((finiteLocalIdelicZFunction_existsUnique v f).exists.choose_spec χ).2 hs

/-- In real coordinates, multiplicative Tamagawa integration is integration
against dx/|x|. The omitted origin has weighted measure zero. -/
private theorem realLocalIntegral_model (w : InfinitePlace F) (hw : w.IsReal) (H : ℝ → ℂ) :
    (∫ u : w.Completionˣ, H (realModel(hw) u.val) ∂μ∞(w)) =
      ∫ t : ℝ, (‖t‖ : ℂ)⁻¹ * H t := by
  classical
  let K := w.Completion
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := borelSpace_units_of_continuousInv₀ K
  let e := realModel(hw)
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let μ := infiniteLocalAdditiveTamagawaMeasure F w
  let D (x : K) : ENNReal := (↑(‖x‖₊ ^ w.mult) : ENNReal)⁻¹
  let ι : Kˣ → K := Units.val
  have hι : MeasurableEmbedding ι := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  have hμ : μ = (volume : Measure ℝ).map e.symm := by
    exact dite_eq_left hw
  have hj : MeasurableEmbedding (e.symm : ℝ → K) := j.symm.toHomeomorph.measurableEmbedding
  have hμ₀ : μ {0} = 0 := by
    rw [hμ, hj.map_apply]
    have hpre : e.symm ⁻¹' ({0} : Set K) = {0} := by
      ext x
      exact e.symm.map_eq_zero_iff
    rw [hpre, measure_singleton]
  have hneμ : ∀ᵐ x ∂μ, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hμ₀
  have hν : ∀ᵐ x ∂μ.withDensity D, x ≠ 0 :=
    (withDensity_absolutelyContinuous μ D).ae_le hneμ
  have hmap : (μ∞(w)).map ι = μ.withDensity D := by
    rw [infiniteLocalMultiplicativeTamagawaMeasure, hι.map_comap, Measure.restrict_eq_self_of_ae_mem]
    exact hν.mono fun x hx ↦ ⟨Units.mk0 x hx, rfl⟩
  have hD : Measurable D := (measurable_coe_nnreal_ennreal.comp ((continuous_nnNorm.pow w.mult).measurable)).inv
  have hfinite : ∀ᵐ x ∂μ, D x < ⊤ := by
    filter_upwards [hneμ] with x hx
    change x ≠ 0 at hx
    simpa [D, hw.mult_eq_one] using hx
  calc
    _ = ∫ x : K, H (e x) ∂((μ∞(w)).map ι) := (hι.integral_map (fun x ↦ H (e x))).symm
    _ = ∫ x : K, (D x).toReal • H (e x) ∂μ := by rw [hmap, integral_withDensity_eq_integral_toReal_smul hD hfinite]
    _ = _ := by
      rw [hμ, hj.integral_map]
      apply integral_congr_ae
      filter_upwards with t
      have hn : ‖e.symm t‖ = ‖t‖ := j.symm.isometry.norm_map_of_map_zero (map_zero e.symm) _
      simp only [D, hw.mult_eq_one, pow_one, ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm,
        e.apply_symm_apply, hn, Complex.real_smul, Complex.ofReal_inv]

private theorem realModelSchwartz (w : InfinitePlace F) (hw : w.IsReal) (f : ℬ(w.Completion)) :
    ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ, g x = test(f) ((realModel(hw)).symm x) := by
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let e : Multiplicative ℝ ≃ₜ* Multiplicative w.Completion :=
    { (realModel(hw)).symm.toAddEquiv.toMultiplicative with
      continuous_toFun := j.symm.continuous
      continuous_invFun := j.continuous }
  let b : ℬ(ℝ) := ⟨f.val ∘ e, schwartzBruhat_mem_comp_equiv e f.property⟩
  obtain ⟨E, hE⟩ := realSchwartzBruhat_equiv
  refine ⟨E.symm b, fun x ↦ (hE (E.symm b) x).symm.trans ?_⟩
  rw [E.apply_symm_apply]
  rfl

section ArchimedeanParameters
local notation "unit(" χ ")" => (circleToComplex).comp χ
private theorem realPlaceUnitary_shape (w : InfinitePlace F) (hw : w.IsReal) (χ : PontryaginDual w.Completionˣ) :
    ∃ (t : ℂ) (a : Fin 2), t.re=0 ∧ realShape[hw,unit(χ),t,a] := by
  let e := (realModel(hw)).symm
  let i : ℝˣ →ₜ* w.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.units_map _⟩
  obtain ⟨p,ht,hp⟩ := (existsUnique_realUnits_character_parameters ((unit(χ)).comp i)
    (fun _ ↦ Circle.norm_coe _)).exists
  exact ⟨p.1,p.2,ht,hp⟩

private theorem complexPlaceUnitary_shape (w : InfinitePlace F) (hw : w.IsComplex) (χ : PontryaginDual w.Completionˣ) :
    ∃ (t : ℂ) (r : ℤ), t.re=0 ∧ complexShape[hw,unit(χ),t,r] := by
  let e := (complexModel(hw)).symm
  let i : ℂˣ →ₜ* w.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.units_map _⟩
  obtain ⟨p,ht,hp⟩ := (existsUnique_complexUnits_character_parameters ((unit(χ)).comp i)
    (fun _ ↦ Circle.norm_coe _)).exists
  exact ⟨p.1,p.2,ht,hp⟩

private theorem realModule_model (w : InfinitePlace F) (hw : w.IsReal) (x : ℝˣ) :
    (((m∞(w) (Units.map (realModel(hw)).symm.toMonoidHom x) : ℝ≥0) : ℝ)) = ‖x.val‖ := by
  have hn : ‖(realModel(hw)).symm x.val‖ = ‖x.val‖ := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero (map_zero (realModel(hw)).symm) x.val
  simp [InfinitePlace.mult,hw,hn]

private theorem complexModule_model (w : InfinitePlace F) (hw : w.IsComplex) (x : ℂˣ) :
    (((m∞(w) (Units.map (complexModel(hw)).symm.toMonoidHom x) : ℝ≥0) : ℝ)) = ‖x.val‖^2 := by
  have hn : ‖(complexModel(hw)).symm x.val‖ = ‖x.val‖ := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry.norm_map_of_map_zero (map_zero (complexModel(hw)).symm) x.val
  simp [InfinitePlace.mult,InfinitePlace.not_isReal_iff_isComplex.mpr hw,hn]

private theorem realChart_shape (w : InfinitePlace F) (hw : w.IsReal) (χ : PontryaginDual w.Completionˣ)
    (t : ℂ) (a : Fin 2) (hc : realShape[hw,unit(χ),t,a]) (z : ℂ) :
    realShape[hw,chart∞[w,χ] z,z+t,a] := by
  intro x
  let u := Units.map (realModel(hw)).symm.toMonoidHom x
  change unit(χ) u * ((((m∞(w) u : ℝ≥0):ℝ)):ℂ)^z = _
  rw [hc x,realModule_model,Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))]
  ring

private theorem complexChart_shape (w : InfinitePlace F) (hw : w.IsComplex) (χ : PontryaginDual w.Completionˣ)
    (t : ℂ) (r : ℤ) (hc : complexShape[hw,unit(χ),t,r]) (z : ℂ) :
    complexShape[hw,chart∞[w,χ] z,z+t,r] := by
  intro x
  let u := Units.map (complexModel(hw)).symm.toMonoidHom x
  change unit(χ) u * ((((m∞(w) u : ℝ≥0):ℝ)):ℂ)^z = _
  rw [hc x,complexModule_model,Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero)))]
  ring

private theorem realDual_shape (w : InfinitePlace F) (hw : w.IsReal) (c : QuasiCharacter w.Completionˣ)
    (t : ℂ) (a : Fin 2) (hc : realShape[hw,c,t,a]) :
    realShape[hw,dualQuasiCharacter m∞(w) h∞(w) c,1-t,a] := by
  intro x
  let u := Units.map (realModel(hw)).symm.toMonoidHom x
  change ((((m∞(w) u : ℝ≥0):ℝ)):ℂ) * c u⁻¹ = _
  rw [map_inv,hc x,realModule_model,Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)),Complex.cpow_one]
  by_cases h : 0<x.val <;> fin_cases a <;> simp [h,div_eq_mul_inv]

private theorem complexDual_shape (w : InfinitePlace F) (hw : w.IsComplex) (c : QuasiCharacter w.Completionˣ)
    (t : ℂ) (r : ℤ) (hc : complexShape[hw,c,t,r]) :
    complexShape[hw,dualQuasiCharacter m∞(w) h∞(w) c,1-t,(-r)] := by
  intro x
  let u := Units.map (complexModel(hw)).symm.toMonoidHom x
  change ((((m∞(w) u : ℝ≥0):ℝ)):ℂ) * c u⁻¹ = _
  rw [map_inv,hc x,complexModule_model,Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero))),Complex.cpow_one,zpow_neg,mul_inv]
  simp only [div_eq_mul_inv,mul_assoc]

end ArchimedeanParameters

private theorem realIntegral_shape (w : InfinitePlace F) (hw : w.IsReal)
    (g : SchwartzMap ℝ ℂ) (c : QuasiCharacter w.Completionˣ) (z : ℂ) (a : Fin 2)
    (hc : realShape[hw,c,z,a]) (hz : 0 < z.re) :
    localIdelicZetaIntegral μ∞(w) (fun x ↦ g (realModel(hw) x)) c =
      mellin (fun x : ℝ ↦ g x + (-1:ℂ)^a.val * g (-x)) z := by
  let e := realModel(hw)
  let H (t : ℝ) := g t * ((‖t‖:ℂ)^z * (if 0 < t then 1 else (-1:ℂ))^a.val)
  let J (t : ℝ) := (‖t‖ : ℂ)⁻¹ * H t
  have he (u : w.Completionˣ) : g (e u.val) * c u = H (e u.val) := by
    let x := Units.map e.toMonoidHom u
    have h := hc x
    rw [show Units.map e.symm.toMonoidHom x = u from Units.ext (e.symm_apply_apply u.val)] at h
    exact congrArg (g (e u.val) * ·) h
  change (∫ u : w.Completionˣ, g (e u.val) * c u ∂μ∞(w)) = _
  rw [integral_congr_ae (.of_forall he)]
  rw [realLocalIntegral_model]
  change (∫ x : ℝ, J x) = _
  let P (t : ℝ) := (t : ℂ) ^ (z-1)
  have hpos {t : ℝ} (ht : 0<t) : J t = P t * g t ∧ J (-t) = P t * ((-1:ℂ)^a.val * g (-t)) := by
    have hne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    simp only [P, J, H, Real.norm_eq_abs, abs_neg, abs_of_pos ht, ite_eq_left ht, one_pow,
      ite_eq_right (not_lt.mpr (neg_nonpos.mpr ht.le)), Complex.cpow_sub _ _ hne, Complex.cpow_one]
    constructor <;> ring
  have hconv (k : SchwartzMap ℝ ℂ) : MellinConvergent (fun t : ℝ ↦ k t) z := by
    apply mellinConvergent_of_isBigO_rpow (a := z.re+1) (b := 0) (k.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    · have h := (k.isBigO_cocompact_rpow (-(z.re+1))).mono (atTop_le_cocompact (α := ℝ))
      apply h.congr' .rfl
      filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
      simp [Real.norm_eq_abs, abs_of_nonneg ht]
    · linarith
    · simpa using ((k.continuous.continuousAt (x := 0)).isBigO_one ℝ).mono nhdsWithin_le_nhds
    · exact hz
  let k := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ) (F := ℂ) g
  have hi₁ : IntegrableOn (fun x ↦ P x * g x) (Ioi (0:ℝ)) := hconv g
  have hi₂ : IntegrableOn (fun x ↦ P x * ((-1:ℂ)^a.val * g (-x))) (Ioi (0:ℝ)) := by
    apply ((hconv k).const_mul ((-1:ℂ)^a.val)).congr
    filter_upwards with x
    change (-1:ℂ)^a.val * (P x * g (-x)) = _
    ring
  have hiPos : IntegrableOn J (Ioi 0) := hi₁.congr (ae_restrict_mem measurableSet_Ioi |>.mono fun t ht ↦ (hpos ht).1.symm)
  have hiNeg : IntegrableOn (fun t ↦ J (-t)) (Ioi 0) := hi₂.congr (ae_restrict_mem measurableSet_Ioi |>.mono fun t ht ↦ (hpos ht).2.symm)
  have hiLeft : IntegrableOn J (Iic 0) := by
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    simpa using hiNeg.comp_neg
  have hneg : (∫ x in Iic (0:ℝ), J x) = ∫ x in Ioi (0:ℝ), J (-x) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 J).symm
  rw [← intervalIntegral.integral_Iic_add_Ioi hiLeft hiPos, hneg]
  rw [setIntegral_congr_fun (f := fun t ↦ J (-t)) measurableSet_Ioi (fun t ht ↦ (hpos ht).2),
    setIntegral_congr_fun (f := J) measurableSet_Ioi (fun t ht ↦ (hpos ht).1), add_comm, ← integral_add hi₁ hi₂]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  change (P t * g t + P t * _) = P t * _
  ring


/-- Splitting the integral into its positive and negative rays gives the
ordinary Mellin transform of the parity projection of the test function. -/
private theorem realLocalZeta_mellin (w : InfinitePlace F) (hw : w.IsReal)
    (f : ℬ(w.Completion)) (χ : PontryaginDual w.Completionˣ) (a : Fin 2)
    (hχ : realShape[hw, ((circleToComplex).comp χ), 0, a])
    (g : SchwartzMap ℝ ℂ) (hg : ∀ x : ℝ, g x = test(f) ((realModel(hw)).symm x))
    {z : ℂ} (hz : 0 < z.re) :
    infiniteLocalIdelicZFunction w f (chart∞[w, χ] z) =
      mellin (fun x : ℝ ↦ g x + (-1:ℂ)^a.val * g (-x)) z := by
  have hc : realShape[hw,chart∞[w,χ] z,z,a] := by
    simpa only [add_zero] using realChart_shape w hw χ 0 a hχ z
  have he : test(f) = fun x ↦ g (realModel(hw) x) := by
    funext x
    simpa only [RingEquiv.symm_apply_apply] using (hg (realModel(hw) x)).symm
  rw [infiniteLocalIdelicZFunction_eq_integral w f χ hz,he]
  exact realIntegral_shape w hw g _ z a hc hz

section TaylorMellin

open Asymptotics
open scoped ContDiff

/-- The Mellin transform of the Taylor polynomial on (0,1] is its sum of
simple fractions. Subtracting it continues the remainder to the left. -/
private theorem mellinTaylor_split (g : ℝ → ℂ) (hg : ContDiff (ℝ) (∞) g)
    (hdec : ∀ t : ℝ, g =O[atTop] (fun x : ℝ ↦ x ^ t)) (N : ℕ)
    (Z : ℂ → ℂ) (hZ : Meromorphic Z) (hag : ∀ z : ℂ, 0 < z.re → Z z = mellin g z) :
    let c (j : ℕ) := iteratedDeriv j g 0 / (j.factorial : ℂ)
    ∃ A : ℂ → ℂ, ∀ s : ℂ, -(N : ℝ) < s.re →
      AnalyticAt ℂ A s ∧ Z =ᶠ[𝓝[≠] s] fun z ↦ A z + ∑ j ∈ Finset.range (N+1), c j / (z+j) := by
  classical
  let c (j : ℕ) := iteratedDeriv j g 0 / (j.factorial : ℂ)
  let P (x : ℝ) := ∑ j ∈ Finset.range (N+1), c j * (x : ℂ)^j
  let cut := (Ioc (0:ℝ) 1).indicator P
  let R := g - cut
  let U := Complex.re ⁻¹' Ioi (-(N : ℝ))
  let A := mellin R
  let Q (z : ℂ) := ∑ j ∈ Finset.range (N+1), c j / (z+j)
  have htaylor (x : ℝ) : P x = taylorWithinEval g N univ 0 x := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k _
    simp only [sub_zero, iteratedDerivWithin_univ, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast, Complex.ofReal_pow, c]
    ring
  have hloc : LocallyIntegrableOn R (Ioi 0) :=
    (hg.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi).sub
      (locallyIntegrableOn_indicator_Ioc (show Continuous P by dsimp only [P]; fun_prop).continuousOn)
  have htop : ∀ p : ℝ, R =O[atTop] (fun x : ℝ ↦ x^p) := by
    intro p
    refine (hdec p).congr' ?_ .rfl
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    simp [R, cut, indicator_of_notMem (fun h : x ∈ Ioc (0:ℝ) 1 ↦ hx.not_ge h.2)]
  have hbot : R =O[𝓝[>] 0] fun x : ℝ ↦ x ^ (-(-(N : ℝ))) := by
    have h := (taylor_isLittleO_univ (x₀ := 0) (n := N) (hg.of_le (by simp))).isBigO.mono
      (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    refine h.congr' ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      simp [R, cut, indicator_of_mem (show t ∈ Ioc (0:ℝ) 1 from ⟨ht.1,ht.2.le⟩), htaylor]
    · simp
  have hopen : IsOpen U := isOpen_Ioi.preimage Complex.continuous_re
  have hdiff : DifferentiableOn ℂ A U := fun z hz ↦
    (mellin_differentiableAt_of_isBigO_rpow hloc (htop _) (lt_add_one z.re) hbot hz).differentiableWithinAt
  have hQ : Meromorphic Q := fun z ↦ MeromorphicAt.fun_sum fun j _ ↦
    (MeromorphicAt.const _ z).div ((MeromorphicAt.id z).add (MeromorphicAt.const _ z))
  have hmer : MeromorphicOn (fun z ↦ Z z - (A z + Q z)) U := fun z hz ↦
    (hZ z).sub (((hdiff.analyticOnNhd hopen z hz).meromorphicAt).add (hQ z))
  have hc (z : ℂ) (hz : 0 < z.re) : HasMellin cut z (Q z) := by
    let r (j : ℕ) (t : ℝ) := c j * (Ioc (0:ℝ) 1).indicator (fun x : ℝ ↦ (x : ℂ)^(j : ℂ)) t
    have hterm (j : ℕ) : HasMellin (r j) z (c j / (z+j)) := by
      have hM := hasMellin_cpow_Ioc (j : ℂ) (s := z) (by simp; positivity)
      have h := hasMellin_const_smul hM.1 (c j)
      rw [hM.2] at h
      simpa only [r, Pi.smul_def, smul_eq_mul, mul_one_div] using h
    have he : cut = fun t ↦ ∑ j ∈ Finset.range (N+1), r j t := by
      funext t
      by_cases ht : t ∈ Ioc (0:ℝ) 1 <;> simp [cut, P, r, ht, Complex.cpow_natCast]
    rw [he]
    exact hasMellin_finset_sum _ r _ z (fun j _ ↦ hterm j)
  have hag' (z : ℂ) (hz : 0 < z.re) : Z z = A z + Q z := by
    have hR := mellinConvergent_of_isBigO_rpow hloc (htop _) (lt_add_one z.re) hbot (by linarith [Nat.cast_nonneg (α := ℝ) N] : - (N:ℝ) < z.re)
    have h := (hasMellin_add hR (hc z hz).1).2
    rw [(hc z hz).2] at h
    rw [hag z hz]
    exact (congrArg (fun u : ℝ → ℂ ↦ mellin u z) (sub_add_cancel g cut).symm).trans h
  have h₁ : (1 : ℂ) ∈ U := by change -(N:ℝ) < 1; linarith [Nat.cast_nonneg (α := ℝ) N]
  have h₀ : meromorphicOrderAt (fun z ↦ Z z - (A z + Q z)) 1 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds
      (show (1 : ℂ) ∈ rightHalf by norm_num [mem_preimage, mem_Ioi]))] with z hz
    exact sub_eq_zero.mpr (hag' z hz)
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt (-(N:ℝ))).isPreconnected
  refine ⟨A, fun s hs ↦ ⟨hdiff.analyticOnNhd hopen s hs, ?_⟩⟩
  exact (meromorphicOrderAt_eq_top_iff.mp (hmer.meromorphicOrderAt_eq_top_of_isPreconnected hconn h₁ hs h₀)).mono
    fun z hz ↦ sub_eq_zero.mp hz

end TaylorMellin

section RealMellinPoles

open scoped ContDiff
open Asymptotics

private theorem schwartzDecay_atTop (g : SchwartzMap ℝ ℂ) (p : ℝ) :
    (g : ℝ → ℂ) =O[atTop] (fun x : ℝ ↦ x ^ p) := by
  refine ((g.isBigO_cocompact_rpow p).mono (atTop_le_cocompact (α := ℝ))).congr' .rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [Real.norm_eq_abs, abs_of_nonneg ht]

/-- At a nonpositive integer the only singular term is its Taylor coefficient
divided by the local coordinate. -/
private theorem mellinTaylor_principalAt (g : SchwartzMap ℝ ℂ) (Z : ℂ → ℂ) (hZ : Meromorphic Z)
    (hag : ∀ z : ℂ, 0 < z.re → Z z = mellin (g : ℝ → ℂ) z) (n : ℕ) :
    let s : ℂ := -(n : ℂ)
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A s ∧ Z =ᶠ[𝓝[≠] s] fun z ↦
      A z + (iteratedDeriv n (g : ℝ → ℂ) 0 / (n.factorial : ℂ)) / (z-s) := by
  classical
  let s : ℂ := -(n : ℂ)
  let c (k : ℕ) := iteratedDeriv k (g : ℝ → ℂ) 0 / (k.factorial : ℂ)
  obtain ⟨A,hA⟩ := mellinTaylor_split g (g.smooth ⊤) (schwartzDecay_atTop g) (n+1) Z hZ hag
  have hs : -((n+1 : ℕ):ℝ) < s.re := by simp [s]
  obtain ⟨ha,he⟩ := hA s hs
  let S := Finset.range (n+1+1)
  have hmem : n ∈ S := Finset.mem_range.mpr (by omega)
  let B (z : ℂ) := ∑ j ∈ S.erase n, c j / (z+j)
  have hb : AnalyticAt ℂ B s := by
    apply Finset.analyticAt_fun_sum
    intro j hj
    apply analyticAt_const.div (analyticAt_id.add analyticAt_const)
    have hne := (Finset.mem_erase.mp hj).1
    exact fun h ↦ hne (Nat.cast_injective (R := ℂ) (by dsimp [s] at h; linear_combination h))
  refine ⟨A+B, ha.add hb, he.mono fun t ht ↦ ?_⟩
  rw [ht]
  change A t + ∑ j ∈ S, c j / (t+j) = (A t + B t) + c n / (t-s)
  rw [← Finset.add_sum_erase S _ hmem]
  dsimp only [B, s]
  rw [sub_neg_eq_add]
  abel

private theorem mellinTaylor_regular (g : SchwartzMap ℝ ℂ) (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hag : ∀ z : ℂ, 0 < z.re → Z z = mellin (g : ℝ → ℂ) z)
    (s : ℂ) (hs : ∀ n : ℕ, s ≠ -(n:ℂ)) : 0 ≤ meromorphicOrderAt Z s := by
  obtain ⟨N,hN⟩ := exists_nat_gt (-s.re)
  obtain ⟨A,hA⟩ := mellinTaylor_split g (g.smooth ⊤) (schwartzDecay_atTop g) N Z (fun z ↦ hZ.meromorphicOn z trivial) hag
  obtain ⟨ha,he⟩ := hA s (by linarith)
  rw [meromorphicOrderAt_congr he]
  apply AnalyticAt.meromorphicOrderAt_nonneg
  apply ha.add
  apply Finset.analyticAt_fun_sum
  intro j _
  exact analyticAt_const.div (analyticAt_id.add analyticAt_const) (fun h ↦ hs j (eq_neg_of_add_eq_zero_left h))

private def parityProfile (g : SchwartzMap ℝ ℂ) (a : Fin 2) : SchwartzMap ℝ ℂ :=
  g + (-1:ℂ)^a.val • (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ) (F := ℂ) g)

private theorem parityProfile_jet (g : SchwartzMap ℝ ℂ) (a : Fin 2) (n : ℕ) :
    iteratedDeriv n (parityProfile g a : ℝ → ℂ) 0 =
      (1 + (-1:ℂ)^(a.val+n)) * iteratedDeriv n (g : ℝ → ℂ) 0 := by
  let k (x : ℝ) := g (-x)
  have hk : ContDiff ℝ (n : ℕ) k := (g.smooth n).comp contDiff_neg
  change iteratedDeriv n ((g : ℝ → ℂ) + (-1:ℂ)^a.val • k) 0 = _
  rw [iteratedDeriv_add (g.smooth n).contDiffAt (g := (-1:ℂ)^a.val • k) (hk.const_smul ((-1:ℂ)^a.val)).contDiffAt,
    iteratedDeriv_const_smul hk.contDiffAt, show iteratedDeriv n k 0 = _ from iteratedDeriv_comp_neg n (g : ℝ → ℂ) 0]
  simp only [neg_zero, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, smul_eq_mul, pow_add]
  ring

private theorem realZeta_principal (w : InfinitePlace F) (hw : w.IsReal) (f : ℬ(w.Completion))
    (χ : PontryaginDual w.Completionˣ) (a : Fin 2) (hχ : realShape[hw, ((circleToComplex).comp χ), 0, a]) (n : ℕ) :
    let s : ℂ := -(n:ℂ)
    let c := (1+(-1:ℂ)^(a.val+n)) * iteratedDeriv n (fun x : ℝ ↦ test(f) ((realModel(hw)).symm x)) 0 / (n.factorial : ℂ)
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A s ∧ (infiniteLocalIdelicZFunction w f ∘ chart∞[w,χ]) =ᶠ[𝓝[≠] s]
      fun z ↦ A z + c / (z-s) := by
  obtain ⟨g,hg⟩ := realModelSchwartz w hw f
  have h := mellinTaylor_principalAt (parityProfile g a) _ (fun z ↦
    ((infiniteLocalIdelicZFunction_existsUnique w f).exists.choose_spec χ).1.meromorphicOn z trivial)
    (fun z hz ↦ realLocalZeta_mellin w hw f χ a hχ g hg hz) n
  rw [parityProfile_jet, show (g : ℝ → ℂ) = _ from funext hg] at h
  exact h

end RealMellinPoles

/-- A simple principal part has a pole precisely when its coefficient is nonzero. -/
private theorem simplePrincipal_order {Z A : ℂ → ℂ} {s c : ℂ} (ha : AnalyticAt ℂ A s)
    (he : Z =ᶠ[𝓝[≠] s] fun z ↦ A z + c/(z-s)) :
    if c=0 then 0 ≤ meromorphicOrderAt Z s else meromorphicOrderAt Z s = -1 := by
  rw [meromorphicOrderAt_congr he]
  split_ifs with hc
  · simpa [hc] using ha.meromorphicOrderAt_nonneg
  · let B (z : ℂ) := c/(z-s)
    have hB : meromorphicOrderAt B s = -1 := by
      change meromorphicOrderAt ((fun _ ↦ c)/(fun z : ℂ ↦ z-s)) s = -1
      have hd : MeromorphicAt (fun z : ℂ ↦ z-s) s := (analyticAt_id.sub analyticAt_const).meromorphicAt
      rw [meromorphicOrderAt_div (MeromorphicAt.const c s) hd,
        meromorphicOrderAt_const, ite_eq_right hc, meromorphicOrderAt_id_sub_const]
      rfl
    change meromorphicOrderAt (A+B) s = -1
    exact (meromorphicOrderAt_add_eq_right_of_lt ha.meromorphicAt
      (hB ▸ (show (-1 : WithTop ℤ) < 0 by decide).trans_le ha.meromorphicOrderAt_nonneg)).trans hB

open scoped ContDiff in
/-- A compactly supported test agreeing with x^n near zero realizes a
nonzero jet of every prescribed degree. -/
private theorem realTest_nonzero_jet (w : InfinitePlace F) (hw : w.IsReal) (n : ℕ) :
    ∃ f : ℬ(w.Completion), iteratedDeriv n (fun x : ℝ ↦ test(f) ((realModel(hw)).symm x)) 0 ≠ 0 := by
  let b : ContDiffBump (0:ℝ) := ⟨1,2,one_pos,one_lt_two⟩
  let p (x : ℝ) := (x^n) • (1:ℂ)
  let h (x : ℝ) := b x • p x
  have hc : HasCompactSupport h := b.hasCompactSupport.smul_right
  have hd : ContDiff (ℝ) (∞) h := by
    exact b.contDiff.smul ((contDiff_id.pow n).smul contDiff_const)
  let g := hc.toSchwartzMap hd
  obtain ⟨E,hE⟩ := realSchwartzBruhat_equiv
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let e : Multiplicative w.Completion ≃ₜ* Multiplicative ℝ :=
    { (realModel(hw)).toAddEquiv.toMultiplicative with
      continuous_toFun := j.continuous
      continuous_invFun := j.symm.continuous }
  let f : ℬ(w.Completion) := ⟨(E g).val ∘ e, schwartzBruhat_mem_comp_equiv e (E g).property⟩
  have hg (x : ℝ) : test(f) ((realModel(hw)).symm x) = h x := by
    change E g (Multiplicative.ofAdd ((realModel(hw)) ((realModel(hw)).symm x))) = _
    exact (hE g _).trans (congrArg h ((realModel(hw)).apply_symm_apply x))
  have he : (fun x : ℝ ↦ test(f) ((realModel(hw)).symm x)) =ᶠ[𝓝 0] p := by
    filter_upwards [b.eventuallyEq_one] with x hx
    refine (hg x).trans ?_
    change b x • p x = p x
    rw [show b x = 1 from hx, one_smul]
  refine ⟨f, ?_⟩
  rw [he.iteratedDeriv_eq n]
  dsimp only [p]
  rw [iteratedDeriv_smul_const (f := fun x : ℝ ↦ x^n) (by fun_prop), iteratedDeriv_fun_pow_zero, ite_eq_left rfl]
  simpa using n.factorial_ne_zero

/-- Paper: Lemma 3.3.2.1(1)(1), p. 138. In the pure sign-parity chart, each
scalar zeta function has at most simple poles. The exponents at which some
test function gives a pole are the nonpositive integers of that parity.
Deviation: Tests against Schwartz–Bruhat functions specify the distributional pole. -/
theorem infiniteLocalIdelicZFunction_real_poles (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) (a : Fin 2)
    (hχ : realShape[hw, ((circleToComplex).comp χ), 0, a]) (s : ℂ) :
    (∀ f : ℬ(w.Completion),
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s) ∧
    ((∃ f : ℬ(w.Completion),
      meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s = -1) ↔
      ∃ k : ℕ, s = -((2 * k + a.val : ℕ) : ℂ)) := by
  classical
  let Z (f : ℬ(w.Completion)) := infiniteLocalIdelicZFunction w f ∘ chart∞[w,χ]
  by_cases hn : ∃ n : ℕ, s = -(n:ℂ)
  · obtain ⟨n,rfl⟩ := hn
    let c (f : ℬ(w.Completion)) := (1+(-1:ℂ)^(a.val+n)) *
      iteratedDeriv n (fun x : ℝ ↦ test(f) ((realModel(hw)).symm x)) 0 / (n.factorial : ℂ)
    have horder (f : ℬ(w.Completion)) : if c f = 0 then 0 ≤ meromorphicOrderAt (Z f) (-(n:ℂ))
        else meromorphicOrderAt (Z f) (-(n:ℂ)) = -1 := by
      obtain ⟨A,hA,he⟩ := realZeta_principal w hw f χ a hχ n
      exact simplePrincipal_order hA he
    refine ⟨fun f ↦ ?_, ?_⟩
    · have h := horder f
      split_ifs at h
      · exact (show (-1 : WithTop ℤ) ≤ 0 by decide).trans h
      · exact h.ge
    · constructor
      · rintro ⟨f,hf⟩
        have hev : Even (a.val+n) := by
          by_contra h
          have ho := (Nat.not_even_iff_odd.mp h).neg_one_pow (α := ℂ)
          have hc : c f = 0 := by simp [c,ho]
          have hreg := horder f
          rw [ite_eq_left hc, show meromorphicOrderAt (Z f) (-(n:ℂ)) = -1 from hf] at hreg
          exact (by decide : ¬(0 : WithTop ℤ) ≤ -1) hreg
        obtain ⟨j,hj⟩ := hev
        have ha := a.isLt
        have he : n = 2*((n-a.val)/2)+a.val := by omega
        exact ⟨(n-a.val)/2, congrArg (fun t : ℕ ↦ -(t:ℂ)) he⟩
      · rintro ⟨k,hk⟩
        have hn : n = 2*k+a.val := Nat.cast_injective (R := ℂ) (neg_injective hk)
        have hev : Even (a.val+n) := ⟨a.val+k, by omega⟩
        obtain ⟨f,hf⟩ := realTest_nonzero_jet w hw n
        have hc : c f ≠ 0 := by
          dsimp only [c]
          rw [hev.neg_one_pow, one_add_one_eq_two]
          exact div_ne_zero (mul_ne_zero (by norm_num) hf) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
        exact ⟨f, by simpa only [ite_eq_right hc] using horder f⟩
  · have hreg (f : ℬ(w.Completion)) : 0 ≤ meromorphicOrderAt (Z f) s := by
      obtain ⟨g,hg⟩ := realModelSchwartz w hw f
      exact mellinTaylor_regular (parityProfile g a) _ ((infiniteLocalIdelicZFunction_existsUnique w f).exists.choose_spec χ).1
        (fun z hz ↦ realLocalZeta_mellin w hw f χ a hχ g hg hz) s (fun n h ↦ hn ⟨n,h⟩)
    refine ⟨fun f ↦ (show (-1 : WithTop ℤ) ≤ 0 by decide).trans (hreg f), ⟨?_,?_⟩⟩
    · rintro ⟨f,hf⟩
      exact absurd (hf ▸ hreg f) (by decide)
    · rintro ⟨k,hk⟩
      exact (hn ⟨_,hk⟩).elim

-- TODO(paper-gap): The right side of (3.3.2.13) has the opposite sign from
-- its gamma quotient. The residue of that quotient in (3.3.2.16) needs +i.
-- In (3.3.2.14) and (3.3.2.17) the conjugate Fourier kernel gives +i to
-- the absolute angular weight. In (3.3.2.21) the proof needs m ≥ 0.
-- The residue formulas below use ordinary Taylor coefficients.

/-- Paper: Lemma 3.3.2.1(2)(1), p. 138. At a real pole, the residue applied
to a test function is twice the Taylor coefficient of the corresponding degree.

Deviation: The formula evaluates ordinary derivatives on the test function. With the printed
scaling D = (2πi)⁻¹∂ₓ, the degree-one residue is +4πi times (Df)(0). For the
distribution derivative defined by negative transpose it is −4πi times (Dδ₀)(f), as
in (3.3.2.7). Equation (3.3.2.20) evaluates D on the test. The degree-one residue of
the separate factor ρ for the library's Fourier convention is +4πi, as discussed in I91. -/
theorem infiniteLocalIdelicZFunction_real_residue (w : InfinitePlace F) (hw : w.IsReal)
    (f : ℬ(w.Completion)) (χ : PontryaginDual w.Completionˣ) (a : Fin 2)
    (hχ : realShape[hw, ((circleToComplex).comp χ), 0, a]) (k : ℕ) :
    let n := 2 * k + a.val
    let s₀ : ℂ := -(n : ℂ)
    Tendsto (fun s : ℂ ↦ (s - s₀) * infiniteLocalIdelicZFunction w f (chart∞[w, χ] s))
      (𝓝[≠] s₀) (𝓝 (2 * iteratedDeriv n (fun x : ℝ ↦ test(f) ((realModel(hw)).symm x)) 0 /
        (n.factorial : ℂ))) := by
  let n := 2*k+a.val
  let s₀ : ℂ := -(n:ℂ)
  let b := iteratedDeriv n (fun x : ℝ ↦ test(f) ((realModel(hw)).symm x)) 0
  have hev : Even (a.val+n) := ⟨a.val+k, by dsimp [n]; omega⟩
  obtain ⟨A,hA,he⟩ := realZeta_principal w hw f χ a hχ n
  let c := 2*b/(n.factorial : ℂ)
  have hnear : (fun s : ℂ ↦ (s-s₀) * infiniteLocalIdelicZFunction w f (chart∞[w,χ] s)) =ᶠ[𝓝[≠] s₀]
      fun s ↦ (s-s₀) * A s + c := by
    filter_upwards [he, self_mem_nhdsWithin] with z hz hzs
    change infiniteLocalIdelicZFunction w f (chart∞[w,χ] z) = A z + (1+(-1:ℂ)^(a.val+n))*b/(n.factorial:ℂ)/(z-s₀) at hz
    rw [hz, hev.neg_one_pow, one_add_one_eq_two, mul_add]
    change _ + (z-s₀)*(c/(z-s₀)) = _ + c
    field_simp [sub_ne_zero.mpr (show z ≠ s₀ from hzs)]
  have hlim : Tendsto (fun z : ℂ ↦ (z-s₀)*A z+c) (𝓝[≠] s₀) (𝓝 c) := by
    have hh : ContinuousAt (fun z : ℂ ↦ (z-s₀)*A z+c) s₀ :=
      ((continuousAt_id.sub continuousAt_const).mul hA.continuousAt).add continuousAt_const
    simpa using hh.tendsto.mono_left (nhdsWithin_le_nhds (s := ({s₀} : Set ℂ)ᶜ))
  exact hlim.congr' hnear.symm

/-- Paper: Lemma 3.3.2.1(2)(2), p. 139. The z-Wirtinger derivative differentiates
in the two real coordinate directions with coefficients 1/2 and −i/2.
Deviation: The scaling by 1/(2πi) is absorbed into the residue formula. -/
def wirtingerDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) / 2

/-- Paper: Lemma 3.3.2.1(2)(2), p. 139. The conjugate-Wirtinger derivative
uses coefficients 1/2 and i/2 in the real coordinate directions.
Deviation: The scaling by 1/(2πi) is absorbed into the residue formula. -/
def wirtingerConjDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2

/-- Paper: Lemma 3.3.2.1(2)(2), p. 139. The Wirtinger derivatives distinguish
the coordinate function from its conjugate. -/
theorem wirtingerDeriv_id_conj (z : ℂ) :
    wirtingerDeriv id z = 1 ∧ wirtingerDeriv star z = 0 ∧
      wirtingerConjDeriv id z = 0 ∧ wirtingerConjDeriv star z = 1 := by
  have hconj : fderiv ℝ (⇑(starRingEnd ℂ)) z = (Complex.conjLIE.toContinuousLinearMap) := by
    have hfun : (⇑Complex.conjLIE : ℂ → ℂ) = (⇑(starRingEnd ℂ) : ℂ → ℂ) := by
      funext w
      exact Complex.conjLIE_apply w
    rw [← hfun]
    exact Complex.conjLIE.toContinuousLinearMap.fderiv
  simp [wirtingerDeriv, wirtingerConjDeriv, hconj, Complex.conjLIE_apply]

open scoped ENNReal in
private theorem complexLocalIntegral_model (w : InfinitePlace F) (hw : w.IsComplex) (H : ℂ → ℂ) :
    (∫ u : w.Completionˣ, H (complexModel(hw) u.val) ∂μ∞(w)) =
      (2:ℂ) * ∫ t : ℂ, ((‖t‖ : ℂ)^2)⁻¹ * H t := by
  classical
  let K := w.Completion
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := borelSpace_units_of_continuousInv₀ K
  let e := complexModel(hw)
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  let μ := infiniteLocalAdditiveTamagawaMeasure F w
  let D (x : K) : ENNReal := (↑(‖x‖₊ ^ w.mult) : ENNReal)⁻¹
  let ι : Kˣ → K := Units.val
  have hι : MeasurableEmbedding ι := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  have hμ : μ = (2 • (volume : Measure ℂ)).map e.symm := by
    exact dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw)
  have hj : MeasurableEmbedding (e.symm : ℂ → K) := j.symm.toHomeomorph.measurableEmbedding
  have hμ₀ : μ {0} = 0 := by
    rw [hμ, hj.map_apply]
    have hpre : e.symm ⁻¹' ({0} : Set K) = {0} := by
      ext x
      exact e.symm.map_eq_zero_iff
    simp [hpre]
  have hneμ : ∀ᵐ x ∂μ, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hμ₀
  have hν : ∀ᵐ x ∂μ.withDensity D, x ≠ 0 :=
    (withDensity_absolutelyContinuous μ D).ae_le hneμ
  have hmap : (μ∞(w)).map ι = μ.withDensity D := by
    rw [infiniteLocalMultiplicativeTamagawaMeasure, hι.map_comap, Measure.restrict_eq_self_of_ae_mem]
    exact hν.mono fun x hx ↦ ⟨Units.mk0 x hx, rfl⟩
  have hD : Measurable D := (measurable_coe_nnreal_ennreal.comp ((continuous_nnNorm.pow w.mult).measurable)).inv
  have hfinite : ∀ᵐ x ∂μ, D x < ⊤ := by
    filter_upwards [hneμ] with x hx
    change x ≠ 0 at hx
    simp [D, hw.mult_eq_two]
    exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (ENNReal.coe_ne_zero.mpr (nnNorm_ne_zero_iff.mpr hx)))
  calc
    _ = ∫ x : K, H (e x) ∂((μ∞(w)).map ι) := (hι.integral_map (fun x ↦ H (e x))).symm
    _ = ∫ x : K, (D x).toReal • H (e x) ∂μ := by rw [hmap, integral_withDensity_eq_integral_toReal_smul hD hfinite]
    _ = _ := by
      rw [hμ, hj.integral_map, show (2 • (volume : Measure ℂ)) = (2 : ℝ≥0∞) • volume by simp [two_smul], integral_smul_measure]
      simp only [ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      have hn : ‖e.symm t‖ = ‖t‖ := j.symm.isometry.norm_map_of_map_zero (map_zero e.symm) _
      simp only [D, hw.mult_eq_two, ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm,
        e.apply_symm_apply, hn, Complex.ofReal_inv, Complex.ofReal_pow, NNReal.coe_pow]


private theorem complexModelSchwartz_iff (w : InfinitePlace F) (hw : w.IsComplex) (g : ℂ → ℂ) :
    (fun x : Multiplicative w.Completion ↦ g (complexModel(hw) x.toAdd)) ∈
        schwartzBruhatSubmodule (Multiplicative w.Completion) ↔ ∃ G : SchwartzMap ℂ ℂ, (G : ℂ → ℂ) = g := by
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  let n := Module.finrank ℝ ℂ
  let L : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin n) := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let v : Multiplicative w.Completion ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin n)) :=
    { toMulEquiv := ((complexModel(hw)).toAddEquiv.trans L.toLinearEquiv.toAddEquiv).toMultiplicative
      continuous_toFun := L.continuous.comp j.continuous
      continuous_invFun := j.symm.continuous.comp L.symm.continuous }
  rw [mem_schwartzBruhatSubmodule_euclidean_iff v]
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, funext fun x ↦ ?_⟩
    have h := hf (Multiplicative.ofAdd ((complexModel(hw)).symm x))
    change f (L ((complexModel(hw)) ((complexModel(hw)).symm x))) = g ((complexModel(hw)) ((complexModel(hw)).symm x)) at h
    change f (L x) = g x
    simpa only [RingEquiv.apply_symm_apply] using h
  · rintro ⟨f,rfl⟩
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f, fun x ↦ ?_⟩
    exact congrArg f (L.symm_apply_apply _)

section AngularMellin

open scoped ContDiff
open Asymptotics
local notation "angRange" => Ioo (-Real.pi) Real.pi
private def angularWeight (r : ℤ) (θ : ℝ) : ℂ := Complex.exp ((r:ℂ) * (θ:ℂ) * Complex.I)

private theorem angularWeight_norm (r : ℤ) (θ : ℝ) : ‖angularWeight r θ‖ = 1 := by
  simp [angularWeight, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem angularWeight_smooth (r : ℤ) : ContDiff (ℝ) (∞) (angularWeight r) := by
  exact (Complex.contDiff_exp (𝕜 := ℝ)).comp ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const)

private def angularProfile (g : ℂ → ℂ) (r : ℤ) (t : ℝ) : ℂ :=
  ∫ θ in angRange, angularWeight r θ * g ((t:ℂ) * angularWeight 1 θ)

private theorem angularProfile_smooth {g : ℂ → ℂ} (hg : ContDiff (ℝ) (∞) g) (r : ℤ) :
    ContDiff (ℝ) (∞) (angularProfile g r) := by
  apply ContDiff.parametric_integral isCompact_Icc Ioo_subset_Icc_self
    (measure_mono Ioo_subset_Icc_self |>.trans_lt (isCompact_Icc.measure_lt_top (μ := volume)) |>.ne)
  change ContDiff ℝ _ (fun p : ℝ × ℝ ↦ angularWeight r p.2 * g ((p.1:ℂ) * angularWeight 1 p.2))
  exact ((angularWeight_smooth r).comp contDiff_snd).mul (hg.comp
    ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul ((angularWeight_smooth 1).comp contDiff_snd)))

private theorem angularProfile_decay {g : ℂ → ℂ} {f : SchwartzMap ℂ ℂ}
    (h : ∀ z, ‖g z‖ ≤ ‖f z‖) (r : ℤ) (p : ℝ) :
    angularProfile g r =O[atTop] (fun x : ℝ ↦ x^p) := by
  obtain ⟨C,hC⟩ := (f.isBigO_cocompact_rpow p).bound
  obtain ⟨R,hR⟩ := (Metric.mem_cocompact_iff_closedBall_compl_subset (0:ℂ)).mp hC
  refine isBigO_iff.mpr ⟨C * volume.real angRange, ?_⟩
  filter_upwards [eventually_gt_atTop (max R 0)] with t ht
  have ht₀ : 0<t := (le_max_right _ _).trans_lt ht
  have hn (θ : ℝ) : ‖(t:ℂ) * angularWeight 1 θ‖ = t := by
    simp [angularWeight_norm, abs_of_pos ht₀]
  have hnorm (θ : ℝ) : ‖angularWeight r θ * g ((t:ℂ)*angularWeight 1 θ)‖ ≤ C * ‖t^p‖ := by
    rw [norm_mul, angularWeight_norm, one_mul]
    have hx : (t:ℂ)*angularWeight 1 θ ∉ Metric.closedBall 0 R := by
      rw [Metric.mem_closedBall, dist_zero_right, hn]
      exact not_le.mpr ((le_max_left _ _).trans_lt ht)
    have hb : ‖f ((t:ℂ)*angularWeight 1 θ)‖ ≤ C * ‖‖(t:ℂ)*angularWeight 1 θ‖^p‖ := hR hx
    rw [hn θ] at hb
    exact (h _).trans hb
  exact (norm_setIntegral_le_of_norm_le_const (measure_mono Ioo_subset_Icc_self |>.trans_lt
    (isCompact_Icc.measure_lt_top (μ := volume))) (fun θ _ ↦ hnorm θ)).trans_eq (by ring)

end AngularMellin

section AngularFubini
open Asymptotics
local notation "angRange" => Ioo (-Real.pi) Real.pi

/-- Absolute integrability in polar coordinates allows angular integration
before taking the Mellin transform. -/
private theorem angularMellin_fubini (g : SchwartzMap ℂ ℂ) (r : ℤ) (z : ℂ) (hz : 0 < z.re) :
    (∫ p in Ioi (0 : ℝ) ×ˢ angRange, (p.1:ℂ)^(z-1) * (angularWeight r p.2 *
      g ((p.1:ℂ)*angularWeight 1 p.2))) = mellin (angularProfile g r) z := by
  let J := fun p : ℝ × ℝ ↦ (p.1:ℂ)^(z-1) * (angularWeight r p.2 * g ((p.1:ℂ)*angularWeight 1 p.2))
  let B (t : ℝ) := ∫ θ in angRange, ‖g ((t:ℂ)*angularWeight 1 θ)‖
  let Bc (t : ℝ) : ℂ := B t
  have hω (j : ℤ) := (angularWeight_smooth j).continuous
  have hfin : volume angRange < ⊤ := (measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top
  have hc : Continuous B := by
    apply continuous_of_dominated (bound := fun _ ↦ SchwartzMap.seminorm ℝ 0 0 g)
    · intro x
      exact (g.continuous.comp (continuous_const.mul (hω 1))).norm.aestronglyMeasurable
    · intro x
      exact .of_forall fun θ ↦ (Real.norm_of_nonneg (norm_nonneg _)).le.trans (g.norm_le_seminorm ℝ _)
    · exact integrableOn_const hfin.ne
    · exact .of_forall fun θ ↦ (g.continuous.comp (Complex.continuous_ofReal.mul continuous_const)).norm
  have he : Bc = angularProfile (fun x ↦ (‖g x‖ : ℂ)) 0 := by
    funext t
    simp [Bc, B, angularProfile, angularWeight, integral_complex_ofReal]
  have hbc : Continuous Bc := Complex.continuous_ofReal.comp hc
  have hdec (p : ℝ) : Bc =O[atTop] fun t : ℝ ↦ t^p := by
    rw [he]
    exact angularProfile_decay (f := g) (fun x ↦ by simp) 0 p
  have hconv : MellinConvergent Bc z := mellinConvergent_of_isBigO_rpow
    (hbc.continuousOn.locallyIntegrableOn measurableSet_Ioi) (hdec _) (lt_add_one z.re)
    (b := 0) (by simpa using (hbc.continuousAt (x := 0)).isBigO_one ℝ |>.mono nhdsWithin_le_nhds) hz
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let ν := (volume : Measure ℝ).restrict angRange
  have hmeas : Measurable J := by
    exact ((Complex.continuous_ofReal.comp continuous_fst).measurable.pow measurable_const).mul
      (((hω r).comp continuous_snd).mul (g.continuous.comp
        ((Complex.continuous_ofReal.comp continuous_fst).mul ((hω 1).comp continuous_snd)))).measurable
  have hInt : Integrable J (μ.prod ν) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    constructor
    · apply Eventually.of_forall
      intro t
      have ht : Continuous (fun θ : ℝ ↦ J (t,θ)) :=
        (continuous_const (y := (t:ℂ)^(z-1))).mul ((hω r).mul (g.continuous.comp
          ((continuous_const (y := (t:ℂ))).mul (hω 1))))
      exact (ht.continuousOn.integrableOn_compact (K := Icc (-Real.pi) Real.pi) isCompact_Icc).mono_set Ioo_subset_Icc_self
    · apply hconv.norm.congr
      filter_upwards with t
      change ‖(t:ℂ)^(z-1) * Bc t‖ = ∫ θ in angRange, ‖J (t,θ)‖
      simp only [J, norm_mul, angularWeight_norm, one_mul, integral_const_mul, Bc, Complex.norm_real,
        Real.norm_of_nonneg (show 0 ≤ B t from integral_nonneg fun _ ↦ norm_nonneg _)]
      rfl
  change (∫ p in Ioi (0:ℝ) ×ˢ angRange, J p) = _
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod J hInt]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  exact integral_const_mul (μ := ν) ((t:ℂ)^(z-1)) (fun θ ↦ angularWeight r θ * g ((t:ℂ)*angularWeight 1 θ))

end AngularFubini

private theorem complexIntegral_shape (w : InfinitePlace F) (hw : w.IsComplex)
    (g : SchwartzMap ℂ ℂ) (c : QuasiCharacter w.Completionˣ) (z : ℂ) (r : ℤ)
    (hc : complexShape[hw,c,z,r]) (hz : 0 < z.re) :
    localIdelicZetaIntegral μ∞(w) (fun x ↦ g (complexModel(hw) x)) c =
      2 * mellin (angularProfile g r) (2*z) := by
  let e := complexModel(hw)
  let H (t : ℂ) := g t * (((‖t‖^2:ℝ):ℂ)^z * (t / (‖t‖:ℂ))^r)
  have he (u : w.Completionˣ) : g (e u.val) * c u = H (e u.val) := by
    let x := Units.map e.toMonoidHom u
    have h := hc x
    rw [show Units.map e.symm.toMonoidHom x = u from Units.ext (e.symm_apply_apply u.val)] at h
    exact congrArg (g (e u.val) * ·) h
  change (∫ u : w.Completionˣ, g (e u.val) * c u ∂μ∞(w)) = _
  rw [integral_congr_ae (.of_forall he)]
  rw [complexLocalIntegral_model, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  congr 1
  rw [← angularMellin_fubini g r (2*z) (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hz)]
  apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  obtain ⟨t,θ⟩ := p
  have ht : 0<t := hp.1
  have ht' : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hn : ‖Complex.polarCoord.symm (t,θ)‖ = t := (Complex.norm_polarCoord_symm _).trans (abs_of_pos ht)
  have ha : Complex.polarCoord.symm (t,θ) = (t:ℂ)*angularWeight 1 θ := by
    simp [Complex.polarCoord_symm_apply, angularWeight, Complex.exp_mul_I]
  have hpow : (((t:ℂ)^2)^z) = (t:ℂ)^(2*z) := by
    rw [pow_two, Complex.mul_cpow_ofReal_nonneg ht.le ht.le]
    rw [show (2:ℂ)*z = z+z by ring, Complex.cpow_add _ _ ht']
  have hr : (angularWeight 1 θ)^r = angularWeight r θ := by
    simp only [angularWeight, Int.cast_one, one_mul, ← Complex.exp_int_mul]
    congr 1
    ring
  dsimp only [H, Prod.fst, Prod.snd]
  rw [hn, ha, Complex.real_smul, mul_div_cancel_left₀ _ ht', hr, Complex.ofReal_pow, hpow, Complex.cpow_sub _ _ ht', Complex.cpow_one]
  field_simp


private theorem complexLocalZeta_mellin (w : InfinitePlace F) (hw : w.IsComplex)
    (f : ℬ(w.Completion)) (χ : PontryaginDual w.Completionˣ) (r : ℤ)
    (hχ : complexShape[hw, ((circleToComplex).comp χ), 0, r])
    (g : SchwartzMap ℂ ℂ) (hg : ∀ x : ℂ, g x = test(f) ((complexModel(hw)).symm x))
    {z : ℂ} (hz : 0 < z.re) :
    infiniteLocalIdelicZFunction w f (chart∞[w, χ] z) = 2 * mellin (angularProfile g r) (2*z) := by
  have hc : complexShape[hw,chart∞[w,χ] z,z,r] := by
    simpa only [add_zero] using complexChart_shape w hw χ 0 r hχ z
  have he : test(f) = fun x ↦ g (complexModel(hw) x) := by
    funext x
    simpa only [RingEquiv.symm_apply_apply] using (hg (complexModel(hw) x)).symm
  rw [infiniteLocalIdelicZFunction_eq_integral w f χ hz,he]
  exact complexIntegral_shape w hw g _ z r hc hz

section AngularJets

open scoped ContDiff
local notation "Sc" => SchwartzMap ℂ ℂ
local notation "angRange" => Ioo (-Real.pi) Real.pi

private def coordD (v : ℂ) : Sc →L[ℂ] Sc := LineDeriv.lineDerivOpCLM ℂ Sc v
private def holD : Sc →L[ℂ] Sc := (2:ℂ)⁻¹ • (coordD 1 - Complex.I • coordD Complex.I)
private def antiD : Sc →L[ℂ] Sc := (2:ℂ)⁻¹ • (coordD 1 + Complex.I • coordD Complex.I)

private theorem coordD_apply (v : ℂ) (g : Sc) (z : ℂ) : coordD v g z = fderiv ℝ g z v :=
  SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _

private theorem holD_apply (g : Sc) : (holD g : ℂ → ℂ) = wirtingerDeriv g := by
  funext z
  change (2:ℂ)⁻¹ * (coordD 1 g z - Complex.I * coordD Complex.I g z) = _
  rw [coordD_apply, coordD_apply, wirtingerDeriv, div_eq_inv_mul]

private theorem antiD_apply (g : Sc) : (antiD g : ℂ → ℂ) = wirtingerConjDeriv g := by
  funext z
  change (2:ℂ)⁻¹ * (coordD 1 g z + Complex.I * coordD Complex.I g z) = _
  rw [coordD_apply, coordD_apply, wirtingerConjDeriv, div_eq_inv_mul]

private theorem coordD_comm (u v : ℂ) (g : Sc) : coordD u (coordD v g) = coordD v (coordD u g) := by
  have h (a b z : ℂ) : coordD a (coordD b g) z = fderiv ℝ (fderiv ℝ g) z a b := by
    rw [coordD_apply, show (coordD b g : ℂ → ℂ) = fun t ↦ fderiv ℝ g t b from funext (coordD_apply b g)]
    rw [fderiv_clm_apply (c := fderiv ℝ (g : ℂ → ℂ)) (u := fun _ ↦ b)
      (((g.smooth 2).fderiv_right (m := 1) (by decide)).differentiable (by decide) _)
      (differentiableAt_const b)]
    simp
  ext z
  rw [h,h]
  exact ((g.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)) u v

private theorem wirtinger_comm (g : Sc) : holD (antiD g) = antiD (holD g) := by
  simp only [holD, antiD, smul_apply, add_apply,
    sub_apply, map_smul, map_add, map_sub, coordD_comm 1 Complex.I g]
  module

private theorem angularWeight_add (j k : ℤ) (θ : ℝ) :
    angularWeight (j+k) θ = angularWeight j θ * angularWeight k θ := by
  simp only [angularWeight, Int.cast_add, add_mul, Complex.exp_add]

private theorem angularWeight_neg (j : ℤ) (θ : ℝ) : angularWeight (-j) θ = star (angularWeight j θ) := by
  simp [angularWeight, ← Complex.exp_conj, mul_assoc]

private theorem directional_wirtinger (g : Sc) (z u : ℂ) :
    fderiv ℝ g z u = u * holD g z + star u * antiD g z := by
  let L := fderiv ℝ g z
  have hU : L u = u.re • L 1 + u.im • L Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    simp [Complex.real_smul]
  change L u = _
  rw [hU, congrFun (holD_apply g) z, congrFun (antiD_apply g) z]
  change _ = u * ((L 1 - Complex.I * L Complex.I)/2) + star u * ((L 1 + Complex.I * L Complex.I)/2)
  simp only [Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im u]
  simp only [star_add, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (L Complex.I * (u.im:ℂ)) * Complex.I_sq

private theorem angularProfile_deriv (g : Sc) (r : ℤ) :
    deriv (angularProfile g r) = fun t ↦ angularProfile (holD g) (r+1) t + angularProfile (antiD g) (r-1) t := by
  funext t
  let H (x θ : ℝ) := angularWeight r θ * g ((x:ℂ)*angularWeight 1 θ)
  have hd : ContDiff ℝ 1 H.uncurry := ((angularWeight_smooth r).of_le (by simp) |>.comp contDiff_snd).mul
    ((g.smooth 1).comp ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul
      ((angularWeight_smooth 1).of_le (by simp) |>.comp contDiff_snd)))
  have hmeas : volume angRange < ⊤ := (measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top
  have h := hasFDerivAt_integral_of_contDiffOn (μ := volume) (f := H) (x₀ := t)
    (u := univ) univ_mem isCompact_Icc hmeas.ne Ioo_subset_Icc_self hd.contDiffOn
  have hv (θ : ℝ) : HasDerivAt (fun x : ℝ ↦ H x θ)
      (angularWeight r θ * fderiv ℝ g ((t:ℂ)*angularWeight 1 θ) (angularWeight 1 θ)) t := by
    apply HasDerivAt.const_mul
    exact g.differentiableAt.hasFDerivAt.comp_hasDerivAt t (by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (angularWeight 1 θ))
  rw [show deriv (angularProfile g r) t = _ from h.hasDerivAt.deriv]
  rw [ContinuousLinearMap.integral_apply]
  · let A (k : ℤ) (f : Sc) (θ : ℝ) := angularWeight k θ * f ((t:ℂ)*angularWeight 1 θ)
    have hi (k : ℤ) (f : Sc) : IntegrableOn (A k f) angRange := by
      have hc : Continuous (A k f) := (angularWeight_smooth k).continuous.mul (f.continuous.comp
        (continuous_const.mul (angularWeight_smooth 1).continuous))
      exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
    change _ = (∫ θ in angRange, A (r+1) (holD g) θ) + ∫ θ in angRange, A (r-1) (antiD g) θ
    rw [← integral_add (hi _ _) (hi _ _)]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro θ _
    change fderiv ℝ (fun x ↦ H x θ) t 1 = _
    rw [fderiv_apply_one_eq_deriv, (hv θ).deriv, directional_wirtinger]
    simp only [A, sub_eq_add_neg, angularWeight_add, angularWeight_neg]
    ring
  · have hc : Continuous (fun θ ↦ fderiv ℝ (fun x ↦ H x θ) t) := by
      have h := hd.contDiffOn.fderiv_left (u := univ) (s := univ) (n := 0) isOpen_univ
      exact (contDiff_zero.mp (contDiffOn_univ.mp (h.comp
        (by fun_prop : ContDiffOn ℝ 0 (fun θ : ℝ ↦ (t,θ)) univ) (fun _ _ ↦ ⟨trivial,trivial⟩))))
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

end AngularJets

section AngularCoefficients
open scoped ContDiff
local notation "Sc" => SchwartzMap ℂ ℂ
local notation "angRange" => Ioo (-Real.pi) Real.pi

private theorem angularWeight_integral (r : ℤ) :
    (∫ θ in angRange, angularWeight r θ) = if r=0 then (2:ℂ)*Real.pi else 0 := by
  by_cases hr : r=0
  · subst r
    simp [angularWeight, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    ring
  rw [ite_eq_right hr, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  let c := (r:ℂ)*Complex.I
  have hne : c ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hr) Complex.I_ne_zero
  have he : angularWeight r = fun θ : ℝ ↦ Complex.exp (c * θ) := by
    funext θ
    dsimp [angularWeight,c]
    congr 1
    ring
  rw [he, integral_exp_mul_complex hne, Complex.ofReal_neg]
  have hphase : Complex.exp (c*Real.pi) = Complex.exp (c*(-Real.pi)) := by
    apply (Complex.exp_eq_exp_iff_exists_int).mpr
    exact ⟨r, by dsimp [c]; ring⟩
  rw [hphase, sub_self, zero_div]

private theorem angularProfile_zero (g : Sc) (r : ℤ) :
    angularProfile g r 0 = (if r=0 then (2:ℂ)*Real.pi else 0) * g 0 := by
  simp only [angularProfile, Complex.ofReal_zero, zero_mul, integral_mul_const, angularWeight_integral]

private def angularShift (d : ℤ) (D : Sc → Sc) : Module.End ℂ (ℤ → Sc → ℂ) where
  toFun h r g := h (r+d) (D g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem angularShift_pow (d : ℤ) (D : Sc → Sc) (n : ℕ) (h : ℤ → Sc → ℂ) (r : ℤ) (g : Sc) :
    (((angularShift d D)^n) h) r g = h (r + n*d) (D^[n] g) := by
  induction n generalizing r g with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    change (((angularShift d D)^n) h) (r+d) (D g) = _
    rw [ih, Function.iterate_succ_apply]
    rw [show r+d+(n:ℤ)*d = r+(n+1:ℕ)*d by push_cast; ring]

/-- After angular integration the binomial expansion of a radial derivative
retains only the mixed derivative of weight opposite to the character. -/
private theorem angularProfile_jet (g : Sc) (r : ℤ) (n : ℕ) :
    iteratedDeriv n (angularProfile g r) 0 =
      ∑ p ∈ Finset.antidiagonal n, (n.choose p.1 : ℂ) *
        ((if r+p.1-p.2=0 then (2:ℂ)*Real.pi else 0) * ((antiD^[p.2]) ((holD^[p.1]) g)) 0) := by
  let L := angularShift 1 holD
  let R := angularShift (-1) antiD
  let V (t : ℝ) (j : ℤ) (f : Sc) := angularProfile f j t
  have hcomm : Commute L R := by
    apply LinearMap.ext
    intro h
    funext j f
    change h (j+1+(-1)) (antiD (holD f)) = h (j+(-1)+1) (holD (antiD f))
    rw [wirtinger_comm]
    rw [show j+1+(-1) = j+(-1)+1 by ring]
  have hiter (k : ℕ) (f : Sc) (j : ℤ) (t : ℝ) :
      iteratedDeriv k (angularProfile f j) t = (((L+R)^k) (V t)) j f := by
    induction k generalizing f j t with
    | zero => rfl
    | succ k ih =>
      rw [iteratedDeriv_succ', angularProfile_deriv, iteratedDeriv_fun_add
        ((angularProfile_smooth ((holD f).smooth ⊤) (j+1)).of_le (by simp) |>.contDiffAt)
        ((angularProfile_smooth ((antiD f).smooth ⊤) (j-1)).of_le (by simp) |>.contDiffAt),
        ih, ih, pow_succ', mul_apply_eq_comp]
      rfl
  rw [hiter, hcomm.add_pow']
  simp only [LinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  change (n.choose p.1) • ((((angularShift 1 holD)^p.1) (((angularShift (-1) antiD)^p.2) (V 0))) r g) = _
  rw [angularShift_pow, angularShift_pow]
  simp only [mul_one, mul_neg_one, V, angularProfile_zero, nsmul_eq_mul, sub_eq_add_neg]

end AngularCoefficients

section ScaledMellin
open scoped ContDiff
open Asymptotics

/-- The complex modulus is the square of the ordinary radius. Substituting
twice the exponent moves the Taylor poles to the half-integers. -/
private theorem angularTaylor_split (g : SchwartzMap ℂ ℂ) (r : ℤ) (N : ℕ) (Z : ℂ → ℂ)
    (hZ : Meromorphic Z) (hag : ∀ z : ℂ, 0<z.re → Z z = 2*mellin (angularProfile g r) (2*z)) :
    let c (j : ℕ) := iteratedDeriv j (angularProfile g r) 0 / (j.factorial:ℂ)
    ∃ A : ℂ → ℂ, ∀ s : ℂ, -(N:ℝ) < 2*s.re → AnalyticAt ℂ A s ∧
      Z =ᶠ[𝓝[≠] s] fun z ↦ A z + ∑ j ∈ Finset.range (N+1), c j / (z+j/2) := by
  let V (z : ℂ) := Z (z/2)/2
  have hm : Meromorphic V := fun t ↦ ((hZ (t/2)).comp_analyticAt (g := fun z : ℂ ↦ z/2) (by fun_prop)).div (.const 2 t)
  have he (z : ℂ) (hz : 0<z.re) : V z = mellin (angularProfile g r) z := by
    have hpos : 0 < (z/2).re := by simpa using half_pos hz
    dsimp [V]
    rw [hag _ hpos, show (2:ℂ)*(z/2) = z by ring]
    ring
  obtain ⟨A,hA⟩ := mellinTaylor_split _ (angularProfile_smooth (g.smooth ⊤) r)
    (angularProfile_decay (f := g) (fun _ ↦ le_rfl) r) N V hm he
  let c (j : ℕ) := iteratedDeriv j (angularProfile g r) 0 / (j.factorial:ℂ)
  refine ⟨fun z ↦ 2*A (2*z), fun s hs ↦ ?_⟩
  obtain ⟨ha,heq⟩ := hA (2*s) (by simpa using hs)
  refine ⟨analyticAt_const.mul (ha.comp (f := fun z : ℂ ↦ 2*z) (by fun_prop)), ?_⟩
  have ht : Tendsto (fun z : ℂ ↦ 2*z) (𝓝[≠] s) (𝓝[≠] (2*s)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(continuous_const.mul continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      (show ∀ᶠ z in 𝓝[≠] s, z ≠ s from self_mem_nhdsWithin).mono (fun _ h ↦ (mul_right_injective₀ (two_ne_zero' ℂ)).ne h)⟩
  filter_upwards [ht heq] with t ht
  change Z (2*t/2)/2 = A (2*t) + ∑ j ∈ Finset.range (N+1), c j / (2*t+j) at ht
  rw [show 2*t/2 = t by ring] at ht
  calc
    _ = 2 * (A (2*t) + ∑ j ∈ Finset.range (N+1), c j / (2*t+j)) := by rw [← ht]; ring
    _ = _ := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [show 2*t+(j:ℂ) = (t+j/2)*2 by ring, div_mul_eq_div_div]
      ring

private theorem angularTaylor_principal (g : SchwartzMap ℂ ℂ) (r : ℤ) (Z : ℂ → ℂ)
    (hZ : Meromorphic Z) (hag : ∀ z : ℂ, 0<z.re → Z z = 2*mellin (angularProfile g r) (2*z)) (n : ℕ) :
    let s : ℂ := -(n:ℂ)/2
    let c := iteratedDeriv n (angularProfile g r) 0 / (n.factorial:ℂ)
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A s ∧ Z =ᶠ[𝓝[≠] s] fun z ↦ A z + c / (z-s) := by
  classical
  let s : ℂ := -(n:ℂ)/2
  let c (k : ℕ) := iteratedDeriv k (angularProfile g r) 0 / (k.factorial:ℂ)
  obtain ⟨A,hA⟩ := angularTaylor_split g r (n+1) Z hZ hag
  have hs : -((n+1:ℕ):ℝ) < 2*s.re := by simp [s]; linarith
  obtain ⟨ha,he⟩ := hA s hs
  let S := Finset.range (n+1+1)
  have hmem : n ∈ S := Finset.mem_range.mpr (by omega)
  let B (z : ℂ) := ∑ j ∈ S.erase n, c j / (z+j/2)
  have hb : AnalyticAt ℂ B s := by
    apply Finset.analyticAt_fun_sum
    intro j hj
    apply analyticAt_const.div (analyticAt_id.add analyticAt_const)
    exact fun h ↦ (Finset.mem_erase.mp hj).1 (Nat.cast_injective (R := ℂ) (by dsimp [s] at h; linear_combination 2*h))
  refine ⟨A+B, ha.add hb, he.mono fun t ht ↦ ?_⟩
  rw [ht]
  change A t + ∑ j ∈ S, c j / (t+j/2) = A t + B t + c n / (t-s)
  rw [← Finset.add_sum_erase S _ hmem]
  dsimp only [B,s]
  rw [neg_div, sub_neg_eq_add]
  abel

private theorem angularTaylor_regular (g : SchwartzMap ℂ ℂ) (r : ℤ) (Z : ℂ → ℂ)
    (hZ : Meromorphic Z) (hag : ∀ z : ℂ, 0<z.re → Z z = 2*mellin (angularProfile g r) (2*z))
    (s : ℂ) (hs : ∀ n : ℕ, s ≠ -(n:ℂ)/2) : 0 ≤ meromorphicOrderAt Z s := by
  obtain ⟨N,hN⟩ := exists_nat_gt (-(2*s.re))
  obtain ⟨A,hA⟩ := angularTaylor_split g r N Z hZ hag
  obtain ⟨ha,he⟩ := hA s (by linarith)
  rw [meromorphicOrderAt_congr he]
  apply AnalyticAt.meromorphicOrderAt_nonneg
  apply ha.add
  apply Finset.analyticAt_fun_sum
  intro j _
  exact analyticAt_const.div (analyticAt_id.add analyticAt_const) (fun h ↦ hs j (by linear_combination h))

end ScaledMellin

/-- A test on a complex completion is a classical Schwartz function in the
complex coordinate used for the local measure. -/
private theorem complexModelSchwartz (w : InfinitePlace F) (hw : w.IsComplex) (f : ℬ(w.Completion)) :
    ∃ g : SchwartzMap ℂ ℂ, (g : ℂ → ℂ) = fun z ↦ test(f) ((complexModel(hw)).symm z) := by
  apply (complexModelSchwartz_iff w hw _).mp
  have he : (fun x : Multiplicative w.Completion ↦ test(f) ((complexModel(hw)).symm ((complexModel(hw)) x.toAdd))) = f.val := by
    funext x
    rw [(complexModel(hw)).symm_apply_apply]
    rfl
  rw [he]
  exact f.property

private theorem matchedAngularDegrees (r : ℤ) (m : ℕ) :
    (m+(-r).toNat) + (m+r.toNat) = r.natAbs+2*m ∧
    r + ((m+(-r).toNat : ℕ):ℤ) - ((m+r.toNat : ℕ):ℤ) = 0 := by
  cases r <;> simp <;> omega

private theorem angularProfile_coefficient (g : SchwartzMap ℂ ℂ) (r : ℤ) (a b : ℕ)
    (hw : r+(a:ℤ)-b=0) :
    iteratedDeriv (a+b) (angularProfile g r) 0 / ((a+b).factorial:ℂ) =
      2*(Real.pi:ℂ) * ((wirtingerConjDeriv^[b]) ((wirtingerDeriv^[a]) (g:ℂ→ℂ))) 0 /
        ((a.factorial:ℂ)*(b.factorial:ℂ)) := by
  classical
  rw [angularProfile_jet, Finset.sum_eq_single_of_mem (a,b) (Finset.mem_antidiagonal.mpr rfl)]
  · simp only [hw, ↓reduceIte]
    have hD : Semiconj (fun f : SchwartzMap ℂ ℂ ↦ (f:ℂ→ℂ)) holD wirtingerDeriv := holD_apply
    have hB : Semiconj (fun f : SchwartzMap ℂ ℂ ↦ (f:ℂ→ℂ)) antiD wirtingerConjDeriv := antiD_apply
    have h := (hB.iterate_right b ((holD^[a]) g)).trans (congrArg (wirtingerConjDeriv^[b]) (hD.iterate_right a g))
    have hv := congrFun h 0
    rw [show (((antiD^[b]) ((holD^[a]) g)) 0) = _ from hv]
    have hfac : ((a+b).choose a : ℂ) * a.factorial * b.factorial = (a+b).factorial := by
      exact_mod_cast (by simpa [Nat.add_sub_cancel_left] using
        Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b) :
        (a+b).choose a * a.factorial * b.factorial = (a+b).factorial)
    apply (div_eq_div_iff (Nat.cast_ne_zero.mpr (a+b).factorial_ne_zero)
      (mul_ne_zero (Nat.cast_ne_zero.mpr a.factorial_ne_zero) (Nat.cast_ne_zero.mpr b.factorial_ne_zero))).mpr
    rw [← hfac]
    ring
  · rintro ⟨i,j⟩ hij hne
    have h := Finset.mem_antidiagonal.mp hij
    have hw' : r+(i:ℤ)-j ≠ 0 := by
      intro he
      apply hne
      exact Prod.ext (by dsimp at h; omega) (by dsimp at h; omega)
    simp [hw']

private theorem principalPart_limit {Z A : ℂ → ℂ} {s c : ℂ} (ha : AnalyticAt ℂ A s)
    (he : Z =ᶠ[𝓝[≠] s] fun z ↦ A z + c/(z-s)) :
    Tendsto (fun z ↦ (z-s)*Z z) (𝓝[≠] s) (𝓝 c) := by
  have hl : ContinuousAt (fun z : ℂ ↦ (z-s)*A z+c) s :=
    ((continuousAt_id.sub continuousAt_const).mul ha.continuousAt).add continuousAt_const
  have ht : Tendsto (fun z : ℂ ↦ (z-s)*A z+c) (𝓝[≠] s) (𝓝 c) := by
    simpa using hl.tendsto.mono_left (nhdsWithin_le_nhds (s := ({s} : Set ℂ)ᶜ))
  apply ht.congr'
  filter_upwards [he,self_mem_nhdsWithin] with z hz hzs
  rw [hz]
  field_simp [sub_ne_zero.mpr (show z ≠ s from hzs)]

/-- Paper: Lemma 3.3.2.1(2)(2), pp. 138–139. At a complex pole the residue
is 2π times the Taylor coefficient of angular weight opposite to the character.
Deviation: This uses unscaled Wirtinger derivatives on the test function,
absorbing the phase and normalization into the Taylor coefficient. -/
theorem infiniteLocalIdelicZFunction_complex_residue (w : InfinitePlace F) (hw : w.IsComplex)
    (f : ℬ(w.Completion)) (χ : PontryaginDual w.Completionˣ) (r : ℤ)
    (hχ : complexShape[hw, ((circleToComplex).comp χ), 0, r]) (m : ℕ) :
    let s₀ : ℂ := -(r.natAbs : ℂ) / 2 - m
    let a := m + (-r).toNat
    let b := m + r.toNat
    let g : ℂ → ℂ := fun z ↦ test(f) ((complexModel(hw)).symm z)
    Tendsto (fun s : ℂ ↦ (s - s₀) * infiniteLocalIdelicZFunction w f (chart∞[w, χ] s))
      (𝓝[≠] s₀) (𝓝 (2 * (Real.pi : ℂ) *
        ((wirtingerConjDeriv^[b]) ((wirtingerDeriv^[a]) g)) 0 /
        ((a.factorial : ℂ) * (b.factorial : ℂ)))) := by
  let a := m + (-r).toNat
  let b := m + r.toNat
  let Z := infiniteLocalIdelicZFunction w f ∘ chart∞[w,χ]
  have hm : Meromorphic Z := fun z ↦ ((infiniteLocalIdelicZFunction_existsUnique w f).exists.choose_spec χ).1.meromorphicOn z trivial
  obtain ⟨g,hg⟩ := complexModelSchwartz w hw f
  obtain ⟨A,hA,he⟩ := angularTaylor_principal g r Z hm
    (fun z hz ↦ complexLocalZeta_mellin w hw f χ r hχ g (congrFun hg) hz) (a+b)
  have ht := principalPart_limit hA he
  have hs : -((a+b:ℕ):ℂ)/2 = -(r.natAbs:ℂ)/2-m := by
    rw [show a+b = r.natAbs+2*m from (matchedAngularDegrees r m).1]
    push_cast
    ring
  rw [hs, angularProfile_coefficient g r a b (matchedAngularDegrees r m).2, hg] at ht
  exact ht

private theorem angularProfile_unmatched (g : SchwartzMap ℂ ℂ) (r : ℤ) (n : ℕ)
    (hn : ¬ ∃ m : ℕ, n = r.natAbs+2*m) : iteratedDeriv n (angularProfile g r) 0 = 0 := by
  rw [angularProfile_jet]
  apply Finset.sum_eq_zero
  rintro ⟨i,j⟩ hij
  have h : i+j=n := Finset.mem_antidiagonal.mp hij
  have hw : r+(i:ℤ)-j ≠ 0 := by
    intro he
    apply hn
    cases r with
    | ofNat k =>
      change (k:ℤ)+(i:ℤ)-j=0 at he
      exact ⟨i, by change n = k+2*i; omega⟩
    | negSucc k =>
      have he' : -(k:ℤ)-1+(i:ℤ)-j=0 := by rw [Int.negSucc_eq] at he; omega
      exact ⟨j, by change n = (k+1)+2*j; omega⟩
  simp [hw]

open scoped ContDiff in
/-- A compactly supported monomial in z and its conjugate realizes every
permitted angular jet. -/
private theorem exists_angularJet (r : ℤ) (a b : ℕ) (hw : r+(a:ℤ)-b=0) :
    ∃ g : SchwartzMap ℂ ℂ, iteratedDeriv (a+b) (angularProfile g r) 0 ≠ 0 := by
  let B : ContDiffBump (0:ℂ) := ⟨1,2,one_pos,one_lt_two⟩
  let p (z : ℂ) := z^a * (star z)^b
  let h (z : ℂ) := B z • p z
  have hc : HasCompactSupport h := B.hasCompactSupport.smul_right
  have hd : ContDiff (ℝ) (∞) h := B.contDiff.smul ((contDiff_id.pow a).mul (Complex.conjLIE.contDiff.pow b))
  let g := hc.toSchwartzMap hd
  have hwPow (k : ℤ) (θ : ℝ) : angularWeight k θ = (angularWeight 1 θ)^k := by
    simp only [angularWeight, Int.cast_one, one_mul, ← Complex.exp_int_mul]
    congr 1
    ring
  have he : angularProfile g r =ᶠ[𝓝 0] fun t : ℝ ↦ (2*(Real.pi:ℂ)) * (t:ℂ)^(a+b) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) zero_lt_one] with t ht
    have ht' : |t| < 1 := by simpa [dist_eq_norm] using ht
    have heval (θ : ℝ) : angularWeight r θ * g ((t:ℂ)*angularWeight 1 θ) = (t:ℂ)^(a+b) := by
      let u := angularWeight 1 θ
      have hu : u ≠ 0 := norm_ne_zero_iff.mp ((angularWeight_norm 1 θ).trans_ne one_ne_zero)
      have hb : B ((t:ℂ)*u) = 1 := B.one_of_mem_closedBall (by
        change dist ((t:ℂ)*u) 0 ≤ 1
        simpa [dist_zero_right, u, angularWeight_norm] using ht'.le)
      have hconj : star u = u⁻¹ := by
        rw [← angularWeight_neg, hwPow, zpow_neg_one]
      change angularWeight r θ * (B ((t:ℂ)*u) • (((t:ℂ)*u)^a * (star ((t:ℂ)*u))^b)) = _
      rw [hb, one_smul, hwPow, star_mul', Complex.star_def, Complex.conj_ofReal]
      change u^r * (((t:ℂ)*u)^a * ((t:ℂ)*star u)^b) = _
      rw [hconj, mul_pow, mul_pow, pow_add]
      have hW : u^r * u^a * (u⁻¹)^b = 1 := by
        rw [← zpow_natCast u a, inv_pow, ← zpow_natCast u b, ← zpow_neg, ← zpow_add₀ hu, ← zpow_add₀ hu,
          ← sub_eq_add_neg, hw, zpow_zero]
      linear_combination ((t:ℂ)^a * (t:ℂ)^b) * hW
    change (∫ θ in Ioo (-Real.pi) Real.pi, angularWeight r θ * g ((t:ℂ)*angularWeight 1 θ)) = _
    simp_rw [heval]
    simp [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi), Complex.real_smul]
    ring_nf
    simp
  refine ⟨g, ?_⟩
  rw [he.iteratedDeriv_eq]
  have hp : (fun t : ℝ ↦ (2*(Real.pi:ℂ))*(t:ℂ)^(a+b)) =
      fun t : ℝ ↦ (t^(a+b)) • (2*(Real.pi:ℂ)) := by funext t; simp [Complex.real_smul, mul_comm]
  rw [hp, iteratedDeriv_smul_const (by fun_prop), iteratedDeriv_fun_pow_zero, ite_eq_left rfl]
  simp [Nat.factorial_ne_zero, Real.pi_ne_zero]

/-- Paper: Lemma 3.3.2.1(1)(2), p. 138. In the pure angular-weight chart,
each scalar zeta function has at most simple poles. The exponents at which
some test function gives a pole are minus half the absolute weight minus a natural number.
Deviation: Tests against Schwartz–Bruhat functions specify the distributional pole. -/
theorem infiniteLocalIdelicZFunction_complex_poles (w : InfinitePlace F) (hw : w.IsComplex)
    (χ : PontryaginDual w.Completionˣ) (r : ℤ)
    (hχ : complexShape[hw, ((circleToComplex).comp χ), 0, r]) (s : ℂ) :
    (∀ f : ℬ(w.Completion),
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s) ∧
    ((∃ f : ℬ(w.Completion),
      meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s = -1) ↔
      ∃ m : ℕ, s = -(r.natAbs : ℂ) / 2 - m) := by
  let Z (f : ℬ(w.Completion)) := infiniteLocalIdelicZFunction w f ∘ chart∞[w,χ]
  have hm (f : ℬ(w.Completion)) : Meromorphic (Z f) := fun z ↦
    ((infiniteLocalIdelicZFunction_existsUnique w f).exists.choose_spec χ).1.meromorphicOn z trivial
  by_cases hn : ∃ n : ℕ, s = -(n:ℂ)/2
  · obtain ⟨n,rfl⟩ := hn
    have horder (f : ℬ(w.Completion)) (g : SchwartzMap ℂ ℂ)
        (hg : ∀ x : ℂ, g x = test(f) ((complexModel(hw)).symm x)) :
        if iteratedDeriv n (angularProfile g r) 0 = 0 then 0 ≤ meromorphicOrderAt (Z f) (-(n:ℂ)/2)
        else meromorphicOrderAt (Z f) (-(n:ℂ)/2) = -1 := by
      obtain ⟨A,hA,he⟩ := angularTaylor_principal g r (Z f) (hm f)
        (fun z hz ↦ complexLocalZeta_mellin w hw f χ r hχ g hg hz) n
      simpa [div_eq_zero_iff, Nat.factorial_ne_zero] using simplePrincipal_order hA he
    refine ⟨fun f ↦ ?_, ⟨?_,?_⟩⟩
    · obtain ⟨g,hg⟩ := complexModelSchwartz w hw f
      have h := horder f g (congrFun hg)
      split_ifs at h
      · exact (show (-1 : WithTop ℤ) ≤ 0 by decide).trans h
      · exact h.ge
    · rintro ⟨f,hf⟩
      obtain ⟨g,hg⟩ := complexModelSchwartz w hw f
      have hd : ∃ m : ℕ, n = r.natAbs+2*m := by
        by_contra h
        have ho := horder f g (congrFun hg)
        rw [ite_eq_left (angularProfile_unmatched g r n h), show meromorphicOrderAt (Z f) (-(n:ℂ)/2) = -1 from hf] at ho
        exact (by decide : ¬(0 : WithTop ℤ) ≤ -1) ho
      obtain ⟨m,hm⟩ := hd
      exact ⟨m, by rw [hm]; push_cast; ring⟩
    · rintro ⟨m,hs⟩
      let a := m+(-r).toNat
      let b := m+r.toNat
      have hn : n=a+b := by
        rw [show a+b = r.natAbs+2*m from (matchedAngularDegrees r m).1]
        apply Nat.cast_injective (R := ℂ)
        push_cast
        linear_combination -2*hs
      obtain ⟨g,hg⟩ := exists_angularJet r a b (matchedAngularDegrees r m).2
      let f : ℬ(w.Completion) := ⟨fun x ↦ g (complexModel(hw) x.toAdd), (complexModelSchwartz_iff w hw _).mpr ⟨g,rfl⟩⟩
      have hval (x : ℂ) : g x = test(f) ((complexModel(hw)).symm x) :=
        congrArg g ((complexModel(hw)).apply_symm_apply x).symm
      have ho := horder f g hval
      rw [ite_eq_right (hn ▸ hg)] at ho
      exact ⟨f,ho⟩
  · have hreg (f : ℬ(w.Completion)) : 0 ≤ meromorphicOrderAt (Z f) s := by
      obtain ⟨g,hg⟩ := complexModelSchwartz w hw f
      exact angularTaylor_regular g r _ (hm f) (fun z hz ↦ complexLocalZeta_mellin w hw f χ r hχ g (congrFun hg) hz) s
        (fun n h ↦ hn ⟨n,h⟩)
    refine ⟨fun f ↦ (show (-1 : WithTop ℤ) ≤ 0 by decide).trans (hreg f), ⟨?_,?_⟩⟩
    · rintro ⟨f,hf⟩
      exact absurd (hf ▸ hreg f) (by decide)
    · rintro ⟨m,hm⟩
      exact (hn ⟨r.natAbs+2*m, by rw [hm]; push_cast; ring⟩).elim

section LocalFunctionalEquation

variable {K : Type*} [NormedField K] [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K] [SigmaCompactSpace K] [MeasurableSpace Kˣ]

local notation "twist(" m "," hm "," χ ")" =>
  quasiCharacterNormTwist m hm ((circleToComplex).comp χ)

/-- Continue Tate's equation from the strip of simultaneous convergence by the
meromorphic identity theorem. -/
private theorem localZeta_fourier_equation (m : Kˣ →* ℝ≥0ˣ) (hm : Continuous m)
    (μ : Measure Kˣ) (T : (K → ℂ) → K → ℂ) (ρ : QuasiCharacter Kˣ → ℂ)
    (hρ : IsLocalTateFactor m hm μ T ρ)
    (Z : ℬ(K) → QuasiCharacter Kˣ → ℂ)
    (hZ : ∀ f χ, MeromorphicNFOn (Z f ∘ twist(m, hm, χ)) univ ∧
      EqOn (Z f ∘ twist(m, hm, χ))
        (fun s ↦ localIdelicZetaIntegral μ test(f) (twist(m, hm, χ) s)) rightHalf)
    (f g : ℬ(K)) (hg : test(g) = T test(f)) (χ : PontryaginDual Kˣ) :
    ∀ᶠ s : ℂ in codiscrete ℂ, let c := twist(m, hm, χ) s
      Z f c = ρ c * Z g (dualQuasiCharacter m hm c) := by
  have hdual (s : ℂ) : dualQuasiCharacter m hm (twist(m, hm, χ) s) =
      twist(m, hm, (χ⁻¹)) (1 - s) := dual_norm_chart m hm χ s
  let D (s : ℂ) := Z f (twist(m, hm, χ) s) -
    ρ (twist(m, hm, χ) s) * Z g (twist(m, hm, (χ⁻¹)) (1 - s))
  have hD : Meromorphic D := fun s ↦ ((hZ f χ).1.meromorphicOn s trivial).sub
    (((hρ.1 χ).meromorphicOn s trivial).mul
      (((hZ g χ⁻¹).1.meromorphicOn (1 - s) trivial).comp_analyticAt
        (g := fun t ↦ 1 - t) (by fun_prop)))
  have hstrip : ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ), s.re ∈ Ioo (0 : ℝ) 1 :=
    nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds (by
      norm_num [mem_preimage, mem_Ioo]))
  have hzero : D =ᶠ[codiscrete ℂ] 0 := by
    apply hD.exists_meromorphicOrderAt_eq_top_iff_eventually_zero.mp
    refine ⟨1 / 2, meromorphicOrderAt_eq_top_iff.mpr ?_⟩
    filter_upwards [hstrip] with s hs
    have hpos : 1 - s ∈ rightHalf := by
      change 0 < (1 - s).re
      simpa using sub_pos.mpr hs.2
    change Z f _ - _ * Z g _ = 0
    rw [sub_eq_zero]
    exact ((hZ f χ).2 hs.1).trans ((hρ.2 f χ s hs).trans (by
      rw [← hg, hdual]
      exact congrArg (ρ _ * ·) ((hZ g χ⁻¹).2 hpos).symm))
  filter_upwards [hzero] with s hs
  exact (sub_eq_zero.mp hs).trans (by rw [hdual])

end LocalFunctionalEquation

/-- Integrability for every test gives a linear functional by integration. -/
private def integralLinearForm {X E : Type*} [MeasurableSpace X] [AddCommGroup E] [Module ℂ E]
    (μ : Measure X) (H : X → E →ₗ[ℂ] ℂ) (hi : ∀ f, Integrable (fun x ↦ H x f) μ) : E →ₗ[ℂ] ℂ where
  toFun f := ∫ x, H x f ∂μ
  map_add' f g := by simp_rw [map_add]; exact integral_add (hi f) (hi g)
  map_smul' a f := by simp_rw [map_smul, smul_eq_mul, RingHom.id_apply]; exact integral_const_mul _ _

private def schwartzPointEval {G : Type*} [CommGroup G] [TopologicalSpace G]
    (x : G) : SchwartzBruhat G →ₗ[ℂ] ℂ :=
  (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype

/-- Scalar evaluations detect holomorphy of a family of Schwartz--Bruhat
distributions, by reflexivity and completeness of the strong dual. -/
private theorem schwartzDistribution_holomorphic {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    {U : Set ℂ} (hU : IsOpen U) (Z : ℂ → StrongDual ℂ (SchwartzBruhat G))
    (h : ∀ f, DifferentiableOn ℂ (fun z ↦ Z z f) U) : VectorHolomorphicOn Z U := by
  let E := SchwartzBruhat G
  have : T2Space E := schwartzBruhat_t2
  let tests : Set (Set E) := {s | Bornology.IsVonNBounded ℂ s}
  have : PolynormableSpace ℂ (StrongDual ℂ E) := (uniformConvergenceCLM_withSeminorms tests
    (fun _ h ↦ h) (by simp [tests, Bornology.sUnion_isVonNBounded_eq_univ]) _
    (norm_withSeminorms ℂ ℂ)).toPolynormableSpace
  have : CompleteSpace (StrongDual ℂ (SchwartzBruhat G)) := schwartzBruhat_strongDual_complete
  have : @QuasiCompleteSpace ℂ (StrongDual ℂ E) _ (IsTopologicalAddGroup.rightUniformSpace _) _ _ := by
    convert (inferInstance : QuasiCompleteSpace ℂ (StrongDual ℂ E))
    exact IsUniformAddGroup.rightUniformSpace_eq
  let e := (schwartzBruhat_reflexive (G := G)).choose
  have he := (schwartzBruhat_reflexive (G := G)).choose_spec
  apply differentiableOn_of_weaklyHolomorphicOn hU Z
  intro L
  let f := e.symm L
  have heq : L ∘ Z = fun z ↦ Z z f := by
    funext z
    exact (congrArg (fun M : StrongDual ℂ (StrongDual ℂ E) ↦ M (Z z)) (e.apply_symm_apply L)).symm.trans (he f (Z z))
  rw [heq]
  exact h f

/-- Local holomorphic families clearing all scalar poles give a meromorphic
map into the strong dual. At a removable point the scalar limits define a
continuous functional by Banach--Steinhaus. -/
private theorem distribution_of_local_clearings {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
    (hol : ∀ {V : Set ℂ}, IsOpen V → ∀ Z : ℂ → StrongDual ℂ E,
      (∀ f, DifferentiableOn ℂ (fun z ↦ Z z f) V) → VectorHolomorphicOn Z V)
    (T : E → ℂ → ℂ) (hNF : ∀ f, MeromorphicNFOn (T f) univ)
    (hloc : ∀ s : ℂ, ∃ (n : ℕ) (V : Set ℂ) (A : ℂ → StrongDual ℂ E),
      IsOpen V ∧ s ∈ V ∧ ∀ f t, t ∈ V → AnalyticAt ℂ (fun z ↦ A z f) t ∧
        (fun z ↦ (z-s)^n * T f z) =ᶠ[𝓝[≠] t] fun z ↦ A z f) :
    let P := {s : ℂ | ∃ f, meromorphicOrderAt (T f) s < 0}
    ∃ Z : ℂ → StrongDual ℂ E, IsVectorMeromorphicOn Z univ P ∧
      ∀ s ∉ P, ∀ f, Z s f = T f s := by
  classical
  let P := {s : ℂ | ∃ f, meromorphicOrderAt (T f) s < 0}
  let U := (univ : Set ℂ) \ P
  have hreg {s : ℂ} (hs : s ∈ U) (f : E) : AnalyticAt ℂ (T f) s :=
    ((hNF f) (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp (not_lt.mp fun h ↦ hs.2 ⟨f,h⟩)
  have hLC (s : ℂ) : ∃ (n : ℕ) (V : Set ℂ) (A : ℂ → StrongDual ℂ E),
      IsOpen V ∧ s ∈ V ∧ (∀ f t, t ∈ V → AnalyticAt ℂ (fun z ↦ A z f) t) ∧
      ∀ t ∈ V, t ≠ s → t ∈ U ∧ ∀ f, T f t = A t f / (t-s)^n := by
    obtain ⟨n,V,A,hV,hVs,hA⟩ := hloc s
    refine ⟨n,V,A,hV,hVs, fun f t ht ↦ (hA f t ht).1, fun t ht hts ↦ ?_⟩
    have hres (f : E) : AnalyticAt ℂ (T f) t ∧ T f t = A t f / (t-s)^n := by
      have hnear : T f =ᶠ[𝓝[≠] t] fun z ↦ A z f / (z-s)^n := by
        filter_upwards [(hA f t ht).2, eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds hts)] with z hz hzs
        exact (eq_div_iff (pow_ne_zero _ (sub_ne_zero.mpr hzs))).mpr ((mul_comm _ _).trans hz)
      have han := (hA f t ht).1.div (g := fun z : ℂ ↦ (z-s)^n) (by fun_prop) (pow_ne_zero _ (sub_ne_zero.mpr hts))
      have he := (((hNF f) (mem_univ t)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds han.meromorphicNFAt).mp hnear
      exact ⟨han.congr he.symm, he.eq_of_nhds⟩
    exact ⟨⟨trivial, fun ⟨f,h⟩ ↦ h.not_ge (hres f).1.meromorphicOrderAt_nonneg⟩, fun f ↦ (hres f).2⟩
  have hcod : Pᶜ ∈ codiscrete ℂ := by
    apply mem_codiscrete_iff_forall_mem_nhdsNE.mpr
    intro s
    obtain ⟨_, V, _, hV, hVs, _, h⟩ := hLC s
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hV.mem_nhds hVs), self_mem_nhdsWithin] with t ht hts
    exact (h t ht hts).1.2
  obtain ⟨hclosed, hdis⟩ := compl_mem_codiscrete_iff.mp hcod
  have hopen : IsOpen U := isOpen_univ.sdiff hclosed
  have hex (s : ℂ) (hs : s ∈ U) : ∃ L : StrongDual ℂ E, ∀ f, L f = T f s := by
    obtain ⟨n,V,A,hV,hVs,_,h⟩ := hLC s
    let Q (z : ℂ) := ((z-s)^n)⁻¹ • A z
    have ht : Tendsto (fun z f ↦ Q z f) (𝓝[≠] s) (𝓝 fun f ↦ T f s) := by
      apply tendsto_pi_nhds.mpr
      intro f
      apply ((hreg hs f).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hV.mem_nhds hVs), self_mem_nhdsWithin] with z hz hzs
      rw [(h z hz hzs).2 f]
      exact div_eq_inv_mul _ _
    exact ⟨continuousLinearMapOfTendsto (f := fun f ↦ T f s) Q ht, fun _ ↦ rfl⟩
  let Z (s : ℂ) : StrongDual ℂ E := if hs : s ∈ U then (hex s hs).choose else 0
  have heval {s : ℂ} (hs : s ∈ U) (f) : Z s f = T f s := by
    simpa only [Z, dite_eq_left hs] using (hex s hs).choose_spec f
  refine ⟨Z, ⟨subset_univ _, hdis, hopen, hol hopen Z (fun f s hs ↦ ?_), ?_⟩,
    fun _ hs f ↦ heval ⟨trivial,hs⟩ f⟩
  · exact (hreg hs f).differentiableAt.differentiableWithinAt.congr (fun t ht ↦ heval ht f) (heval hs f)
  · intro s _
    obtain ⟨n,V,A,hV,hVs,ha,h⟩ := hLC s
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hVs)
    refine ⟨n,r,A,hr, fun t ht ↦ (h t (hball ht.1) ht.2).1,
      hol Metric.isOpen_ball A (fun f t ht ↦
        (ha f t (hball ht)).differentiableAt.differentiableWithinAt), ?_⟩
    intro t ht
    obtain ⟨hU,hval⟩ := h t (hball ht.1) ht.2
    ext f
    change A t f = (t-s)^n * Z t f
    rw [heval hU, hval f]
    field_simp [sub_ne_zero.mpr (show t ≠ s from ht.2)]

/-- The positive and reflected positive half-planes cover the exponent plane.
A power clearing the scalar Tate factor clears every test on the second chart. -/
private theorem distribution_of_reflected_integral {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
    (hol : ∀ {V : Set ℂ}, IsOpen V → ∀ Z : ℂ → StrongDual ℂ E,
      (∀ f, DifferentiableOn ℂ (fun z ↦ Z z f) V) → VectorHolomorphicOn Z V)
    (T : E → ℂ → ℂ) (hNF : ∀ f, MeromorphicNFOn (T f) univ) (ρ : ℂ → ℂ) (hρ : Meromorphic ρ)
    (I J : ℂ → StrongDual ℂ E)
    (hI : ∀ f t, t ∈ rightHalf → AnalyticAt ℂ (fun z ↦ I z f) t)
    (hJ : ∀ f t, t ∈ rightHalf → AnalyticAt ℂ (fun z ↦ J z f) t)
    (hr : ∀ f t, t ∈ rightHalf → T f t = I t f)
    (hl : ∀ f t, 1-t ∈ rightHalf → T f =ᶠ[𝓝[≠] t] fun z ↦ ρ z * J (1-z) f) :
    let P := {s : ℂ | ∃ f, meromorphicOrderAt (T f) s < 0}
    ∃ Z : ℂ → StrongDual ℂ E, IsVectorMeromorphicOn Z univ P ∧
      ∀ s ∉ P, ∀ f, Z s f = T f s := by
  have hO : IsOpen rightHalf := isOpen_Ioi.preimage Complex.continuous_re
  apply distribution_of_local_clearings hol T hNF
  intro s
  by_cases hs : s ∈ rightHalf
  · refine ⟨0,rightHalf,I,hO,hs,fun f t ht ↦ ⟨hI f t ht,?_⟩⟩
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hO.mem_nhds ht)] with z hz
    simpa only [pow_zero, one_mul] using hr f z hz
  · obtain ⟨n,hn⟩ := hρ s
    let R (z : ℂ) := (z-s)^n * ρ z
    have hR : AnalyticAt ℂ R s := hn
    let V := {z : ℂ | AnalyticAt ℂ R z} ∩ ((fun z : ℂ ↦ 1-z) ⁻¹' rightHalf)
    have hVs : s ∈ V := ⟨hR, by change 0 < (1-s).re; change ¬0 < s.re at hs; simp; linarith⟩
    let A (z : ℂ) := R z • J (1-z)
    refine ⟨n,V,A,(isOpen_analyticAt ℂ R).inter (hO.preimage (continuous_const.sub continuous_id)),hVs,
      fun f t ht ↦ ⟨?_,?_⟩⟩
    · exact ht.1.mul ((hJ f (1-t) ht.2).comp (f := fun z : ℂ ↦ 1-z) (by fun_prop))
    · filter_upwards [hl f t ht.2] with z hz
      change (z-s)^n * T f z = ((z-s)^n * ρ z) * J (1-z) f
      rw [hz, mul_assoc]


/-- Integration against a continuous weight on a compact set is continuous
in the Schwartz--Bruhat topology. -/
private theorem compactIntegralForm {E X : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [BarrelledSpace ℂ E] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (K : Set X) (hK : IsCompact K)
    (H : X → E →ₗ[ℂ] ℂ) (hf : ∀ f : E, Continuous (fun x ↦ H x f))
    (he : ∀ x, Continuous (fun f ↦ ‖H x f‖)) (I : E → X → ℂ) (hI : ∀ x f, H x f = I f x) :
    ∃ L : StrongDual ℂ E, ∀ f, L f = ∫ x in K, I f x ∂μ := by
  classical
  let q (x : K) := (normSeminorm ℂ ℂ).comp (H x.val)
  have hb : BddAbove (range q) := by
    apply Seminorm.bddAbove_range_iff.mpr
    intro f
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hf f).continuousOn
    exact ⟨B, forall_mem_range.mpr fun x ↦ hB x.val x.property⟩
  let Q : Seminorm ℂ E := ⨆ x, q x
  have hQ : Continuous Q := by
    dsimp only [Q]
    rw [Seminorm.coe_iSup_eq hb]
    exact Seminorm.continuous_iSup q (fun x ↦ he x.val) hb
  have hle (x : X) (hx : x ∈ K) (f : E) : ‖H x f‖ ≤ Q f := (le_ciSup hb (⟨x,hx⟩ : K)) f
  let L := integralLinearForm (μ.restrict K) H fun f ↦ (hf f).continuousOn.integrableOn_compact hK
  let C := (μ K).toNNReal
  refine ⟨⟨L, ?_⟩, fun f ↦ integral_congr_ae (Eventually.of_forall fun x ↦ hI x f)⟩
  apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L
  intro _
  apply Seminorm.continuous_of_le (q := C • Q) (hQ.const_smul C)
  intro f
  change ‖∫ x in K, H x f ∂μ‖ ≤ C * Q f
  calc
    _ ≤ ∫ _ in K, Q f ∂μ := by
      refine (norm_integral_le_integral_norm _).trans (integral_mono_ae
        ((hf f).continuousOn.integrableOn_compact hK).norm (integrableOn_const hK.measure_lt_top.ne) ?_)
      exact (ae_restrict_mem hK.isClosed.measurableSet).mono fun x hx ↦ hle x hx f
    _ = _ := by simp [C, measureReal_def, smul_eq_mul, ENNReal.coe_toNNReal_eq_toReal]

private theorem schwartzCompactIntegral {G X : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (K : Set X) (hK : IsCompact K)
    (ι : X → G) (hι : Continuous ι) (c : X → ℂ) (hc : Continuous c) :
    ∃ L : StrongDual ℂ (SchwartzBruhat G), ∀ f, L f = ∫ x in K, f (ι x) * c x ∂μ := by
  have : BarrelledSpace ℂ (SchwartzBruhat G) := schwartzBruhat_barrelled
  let H (x : X) := c x • schwartzPointEval (ι x)
  have he (x : X) (f : SchwartzBruhat G) : H x f = c x * f (ι x) := rfl
  have hcf (f : SchwartzBruhat G) : Continuous (fun x ↦ H x f) := hc.mul ((schwartzBruhat_continuous (G := G) f).comp hι)
  have hce (x : X) : Continuous (fun f ↦ ‖H x f‖) := by
    have hnorm (f : SchwartzBruhat G) : ‖H x f‖ = ‖c x‖ * ‖f (ι x)‖ := norm_mul _ _
    exact (continuous_const.mul (schwartzBruhat_evalNorm_continuous (ι x))).congr (fun f ↦ (hnorm f).symm)
  exact compactIntegralForm μ K hK H hcf hce (fun f x ↦ f (ι x) * c x)
    (fun x f ↦ (he x f).trans (mul_comm _ _))


section DistributionalContinuation

variable {K : Type*} [NormedField K] [LocallyCompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSpace Kˣ] [BorelSpace Kˣ]
local notation "twist(" m "," h "," η ")" => quasiCharacterNormTwist m h ((circleToComplex).comp η)

/-- Compact exhaustions and Banach--Steinhaus give continuity in the test
function whenever all the local integrals converge. -/
private theorem localIntegralDistribution (μ : Measure Kˣ) [IsFiniteMeasureOnCompacts μ]
    (c : QuasiCharacter Kˣ) (hi : ∀ f : ℬ(K), Integrable (fun u : Kˣ ↦ test(f) u.val * c u) μ) :
    ∃ L : StrongDual ℂ (ℬ(K)), ∀ f, L f = localIdelicZetaIntegral μ test(f) c := by
  let : SecondCountableTopology Kˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : LocallyCompactSpace Kˣ := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).locallyCompactSpace
  let : SecondCountableTopology (Multiplicative K) := ‹SecondCountableTopology K›
  let : LocallyCompactSpace (Multiplicative K) := ‹LocallyCompactSpace K›
  have : BarrelledSpace ℂ (ℬ(K)) := schwartzBruhat_barrelled
  let B := CompactExhaustion.choice Kˣ
  choose L hL using fun n ↦ schwartzCompactIntegral (G := Multiplicative K) μ (B n) (B.isCompact n)
    (fun u ↦ Multiplicative.ofAdd u.val) (continuous_ofAdd.comp Units.continuous_val) c c.continuous
  let V (f : ℬ(K)) := localIdelicZetaIntegral μ test(f) c
  have ht : Tendsto (fun n f ↦ L n f) atTop (𝓝 V) := by
    apply tendsto_pi_nhds.mpr
    intro f
    simp_rw [hL]
    have h := tendsto_setIntegral_of_monotone (fun n ↦ (B.isCompact n).isClosed.measurableSet)
      (OrderHomClass.mono B) ((hi f).integrableOn (s := ⋃ n, B n))
    simpa only [V, localIdelicZetaIntegral, B.iUnion_eq, Measure.restrict_univ] using h
  exact ⟨continuousLinearMapOfTendsto (f := V) L ht, fun _ ↦ rfl⟩

private theorem exists_localIntegralFamily
    (m : Kˣ →* ℝ≥0ˣ) (hm : Continuous m) (μ : Measure Kˣ) [IsFiniteMeasureOnCompacts μ]
    (hint : ∀ f : ℬ(K), ∀ χ z, z ∈ rightHalf →
      Integrable (fun u : Kˣ ↦ test(f) u.val * twist(m,hm,χ) z u) μ) :
    ∃ I : PontryaginDual Kˣ → ℂ → StrongDual ℂ (ℬ(K)), ∀ η z, z ∈ rightHalf → ∀ f : ℬ(K),
      I η z f = localIdelicZetaIntegral μ test(f) (twist(m,hm,η) z) := by
  classical
  have hex (η : PontryaginDual Kˣ) (z : ℂ) : ∃ L : StrongDual ℂ (ℬ(K)), ∀ _ : z ∈ rightHalf,
      ∀ f : ℬ(K), L f = localIdelicZetaIntegral μ test(f) (twist(m,hm,η) z) := by
    by_cases hz : z ∈ rightHalf
    · refine (localIntegralDistribution μ (twist(m,hm,η) z) (fun f ↦ hint f η z hz)).elim fun L hL ↦ ?_
      exact ⟨L,fun _ ↦ hL⟩
    · exact ⟨0, fun h ↦ (hz h).elim⟩
  exact ⟨fun η z ↦ (hex η z).choose, fun η z ↦ (hex η z).choose_spec⟩

private theorem distribution_of_chart_equation {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
    (hol : ∀ {V : Set ℂ}, IsOpen V → ∀ Z : ℂ → StrongDual ℂ E,
      (∀ f, DifferentiableOn ℂ (fun z ↦ Z z f) V) → VectorHolomorphicOn Z V)
    (T T' : E → ℂ → ℂ) (hNF : ∀ f, MeromorphicNFOn (T f) univ) (ρ : ℂ → ℂ) (hρ : Meromorphic ρ)
    (I J : ℂ → StrongDual ℂ E) (FT : E →L[ℂ] E)
    (ha : ∀ f t, t ∈ rightHalf → AnalyticAt ℂ (T f) t)
    (hb : ∀ f t, t ∈ rightHalf → AnalyticAt ℂ (T' f) t)
    (hi : ∀ f t, t ∈ rightHalf → T f t = I t f) (hj : ∀ f t, t ∈ rightHalf → T' f t = J t f)
    (he : ∀ f, T f =ᶠ[codiscrete ℂ] fun z ↦ ρ z * T' (FT f) (1-z)) :
    let P := {s : ℂ | ∃ f, meromorphicOrderAt (T f) s < 0}
    ∃ Z : ℂ → StrongDual ℂ E, IsVectorMeromorphicOn Z univ P ∧
      ∀ s ∉ P, ∀ f, Z s f = T f s := by
  have hO : IsOpen rightHalf := isOpen_Ioi.preimage Complex.continuous_re
  apply distribution_of_reflected_integral hol T hNF ρ hρ I (fun t ↦ (J t).comp FT)
  · exact fun f t ht ↦ (ha f t ht).congr ((show ∀ᶠ z in 𝓝 t, z ∈ rightHalf from hO.mem_nhds ht).mono fun z hz ↦ (hi f z hz))
  · exact fun f t ht ↦ (hb (FT f) t ht).congr ((show ∀ᶠ z in 𝓝 t, z ∈ rightHalf from hO.mem_nhds ht).mono fun z hz ↦ (hj (FT f) z hz))
  · exact hi
  · intro f t ht
    filter_upwards [(he f).filter_mono (nhdsNE_le_codiscrete t), eventually_nhdsWithin_of_eventually_nhds
      ((hO.preimage (continuous_const.sub continuous_id)).mem_nhds ht)] with z hz hpos
    exact hz.trans (congrArg (ρ z * ·) (hj (FT f) _ hpos))

/-- A local Tate equation continues distributions from their half-plane of
integration. The clearing power depends on the place and parameter only. -/
private theorem localZeta_distribution
    (m : Kˣ →* ℝ≥0ˣ) (hm : Continuous m) (μ : Measure Kˣ) [IsFiniteMeasureOnCompacts μ]
    (ν : Measure K) [ν.IsAddHaarMeasure] (ψ : K → Circle) (hψ : IsTamagawaSelfDual ν ψ)
    (ρ : QuasiCharacter Kˣ → ℂ) (hρ : IsLocalTateFactor m hm μ (tamagawaFourier ν ψ) ρ)
    (Z : ℬ(K) → QuasiCharacter Kˣ → ℂ)
    (hZ : ∀ f χ, MeromorphicNFOn (Z f ∘ twist(m,hm,χ)) univ ∧ EqOn (Z f ∘ twist(m,hm,χ))
      (fun z ↦ localIdelicZetaIntegral μ test(f) (twist(m,hm,χ) z)) rightHalf)
    (hint : ∀ f : ℬ(K), ∀ χ z, z ∈ rightHalf →
      Integrable (fun u : Kˣ ↦ test(f) u.val * twist(m,hm,χ) z u) μ)
    (χ : PontryaginDual Kˣ) :
    let P := {s : ℂ | ∃ f, meromorphicOrderAt (Z f ∘ twist(m,hm,χ)) s < 0}
    ∃ D : ℂ → StrongDual ℂ (ℬ(K)), IsVectorMeromorphicOn D univ P ∧
      ∀ s ∉ P, ∀ f, D s f = Z f (twist(m,hm,χ) s) := by
  classical
  let : SecondCountableTopology (Multiplicative K) := ‹SecondCountableTopology K›
  let : LocallyCompactSpace (Multiplicative K) := ‹LocallyCompactSpace K›
  have : BarrelledSpace ℂ (ℬ(K)) := schwartzBruhat_barrelled
  refine (exists_localSchwartzFourierMap ν ψ hψ).elim fun FT hFT ↦ ?_
  refine (exists_localIntegralFamily m hm μ hint).elim fun I hI ↦ ?_
  let T (η : PontryaginDual Kˣ) (f : ℬ(K)) := Z f ∘ twist(m,hm,η)
  have hO : IsOpen rightHalf := isOpen_Ioi.preimage Complex.continuous_re
  have ha (η) (f : ℬ(K)) (t : ℂ) (ht : t ∈ rightHalf) : AnalyticAt ℂ (T η f) t := by
    apply (localIdelicZetaIntegral_analyticAt m hm μ test(f) η 0 (fun z hz ↦ hint f η z hz) t ht).congr
    exact (show ∀ᶠ z in 𝓝 t, z ∈ rightHalf from hO.mem_nhds ht).mono fun z hz ↦ ((hZ f η).2 hz).symm
  have hi (η) (f : ℬ(K)) (t : ℂ) (ht : t ∈ rightHalf) : T η f t = I η t f :=
    ((hZ f η).2 ht).trans (hI η t ht f).symm
  have he (f : ℬ(K)) : T χ f =ᶠ[codiscrete ℂ] fun z ↦ ρ (twist(m,hm,χ) z) * T χ⁻¹ (FT f) (1-z) := by
    apply (localZeta_fourier_equation m hm μ (tamagawaFourier ν ψ) ρ hρ Z hZ f (FT f) (hFT f) χ).mono
    intro z hz
    exact hz.trans (congrArg (fun c ↦ ρ (twist(m,hm,χ) z) * Z (FT f) c) (dual_norm_chart m hm χ z))
  exact distribution_of_chart_equation (E := ℬ(K)) (fun hV D ↦ schwartzDistribution_holomorphic (G := Multiplicative K) hV D)
    (T χ) (T χ⁻¹) (fun f ↦ (hZ f χ).1) (ρ ∘ twist(m,hm,χ)) (fun t ↦ (hρ.1 χ).meromorphicOn t trivial)
    (I χ) (I χ⁻¹) FT (ha χ) (ha χ⁻¹) (hi χ) (hi χ⁻¹) he

end DistributionalContinuation


/-- Paper: §3.3.2, p. 137. In each archimedean chart the local zeta function
is meromorphic with values in the strong dual of the test space.
Deviation: Agreement with scalar normal form is required off the
distributional poles, where evaluation on a test function is regular. -/
theorem infiniteLocalIdelicZFunction_distribution (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) :
    let poles := {s : ℂ | ∃ f : ℬ(w.Completion),
      meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s < 0}
    ∃ Z : ℂ → StrongDual ℂ (ℬ(w.Completion)), IsVectorMeromorphicOn Z univ poles ∧
      ∀ s ∉ poles, ∀ f, Z s f = infiniteLocalIdelicZFunction w f (chart∞[w, χ] s) := by
  let : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let : μ∞(w).IsHaarMeasure := infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  let : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure := infiniteLocalAdditiveTamagawaMeasure_haar F w
  exact localZeta_distribution m∞(w) h∞(w) μ∞(w) _ _ (infiniteLocalAdditiveTamagawaMeasure_selfDual w)
    _ (infiniteLocalTateFactor_spec w) (infiniteLocalIdelicZFunction w)
    (fun f η ↦ (infiniteLocalIdelicZFunction_existsUnique w f).exists.choose_spec η)
    (fun f η _ hz ↦ infiniteLocalIdelicZetaIntegral_integrable w f η hz) χ


/-- Paper: Equation (3.3.2.11), p. 139. The archimedean local functional
equation holds between meromorphic continuations with the standard Fourier transform.
Deviation: Equality is expressed off a discrete set of exponents. -/
theorem infiniteLocalIdelicZFunction_functionalEquation (w : InfinitePlace F) (f : ℬ(w.Completion)) :
    ∃ fHat : ℬ(w.Completion), test(fHat) = F∞(w) test(f) ∧
      ∀ χ : PontryaginDual w.Completionˣ, ∀ᶠ s : ℂ in codiscrete ℂ,
        let c := chart∞[w, χ] s
        infiniteLocalIdelicZFunction w f c = infiniteLocalTateFactor w c *
          infiniteLocalIdelicZFunction w fHat (dualQuasiCharacter m∞(w) h∞(w) c) := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  obtain ⟨g, hg⟩ := exists_localSchwartzFourier _ _ (infiniteLocalAdditiveTamagawaMeasure_selfDual w) f
  refine ⟨g, hg, localZeta_fourier_equation _ _ _ _ _ (infiniteLocalTateFactor_spec w)
    (infiniteLocalIdelicZFunction w) (fun u ↦ (infiniteLocalIdelicZFunction_existsUnique w u).exists.choose_spec)
    f g hg⟩

/-- Paper: Equation (3.3.2.11), p. 139. The finite-place local functional
equation holds between meromorphic continuations with the standard Fourier transform.
Deviation: Equality is expressed off a discrete set of exponents. -/
theorem finiteLocalIdelicZFunction_functionalEquation (v : Primes) (f : ℬ(v.adicCompletion F)) :
    ∃ fHat : ℬ(v.adicCompletion F), test(fHat) = F𝔭(v) test(f) ∧
      ∀ χ : PontryaginDual (v.adicCompletion F)ˣ, ∀ᶠ s : ℂ in codiscrete ℂ,
        let c := chart𝔭[v, χ] s
        finiteLocalIdelicZFunction v f c = finiteLocalTateFactor v c *
          finiteLocalIdelicZFunction v fHat (dualQuasiCharacter m𝔭(v) h𝔭(v) c) := by
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  obtain ⟨g, hg⟩ := exists_localSchwartzFourier _ _ (finiteLocalAdditiveTamagawaMeasure_selfDual F v) f
  refine ⟨g, hg, localZeta_fourier_equation _ _ _ _ _ (finiteLocalTateFactor_spec v)
    (finiteLocalIdelicZFunction v) (fun u ↦ (finiteLocalIdelicZFunction_existsUnique v u).exists.choose_spec)
    f g hg⟩

section FiniteBall

local notation "O(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v : Set (HeightOneSpectrum.adicCompletion F v))
local notation "ballTest(" v ")" => (O(v)).indicator (fun _ ↦ (1 : ℂ))
local notation "U(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v).units

/-- The integer ring is a compact open test set. -/
private theorem finiteBall_test (v : Primes) :
    ∃ f : ℬ(v.adicCompletion F), test(f) = ballTest(v) := by
  have hcl : IsClopen O(v) := ⟨Valued.isClosed_valuationSubring _, Valued.isOpen_valuationSubring _⟩
  have hc : IsCompact O(v) := isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
  obtain ⟨f, hf⟩ := (mem_finitePlaceSchwartz_iff F v (ballTest(v))).2
    ⟨(LocallyConstant.charFn ℂ hcl).isLocallyConstant,
      hc.of_isClosed_subset isClosed_closure (closure_minimal support_indicator_subset hcl.1)⟩
  exact ⟨f, funext hf⟩

/-- For the discrete normalized norm, the open unit ball is the closed ball
of radius the inverse residue cardinality. -/
private theorem finite_norm_lt_one (v : Primes) (u : (v.adicCompletion F)ˣ) :
    ‖u.val‖ < 1 ↔ ‖u.val‖ ≤ (q(v) : ℝ)⁻¹ := by
  have hq : 1 < (q(v) : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hnorm : ‖u.val‖ = (q(v) : ℝ) ^ WithZero.log (Valued.v u.val) := by
    rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ (by simp [u.ne_zero]),
      NNReal.coe_zpow]
    rfl
  rw [hnorm, ← zpow_neg_one, ← zpow_zero (q(v) : ℝ), zpow_lt_zpow_iff_right₀ hq,
    zpow_le_zpow_iff_right₀ hq]
  omega

/-- Changing variables by a local unit multiplies the zeta integral by its character value. -/
private theorem finiteZeta_dilate (v : Primes) (f : v.adicCompletion F → ℂ)
    (c : QuasiCharacter (v.adicCompletion F)ˣ) (a : (v.adicCompletion F)ˣ) :
    localIdelicZetaIntegral μ𝔭(v) (fun x ↦ f (a.inv * x)) c =
      c a * localIdelicZetaIntegral μ𝔭(v) f c := by
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let : μ𝔭(v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  rw [localIdelicZetaIntegral, ← integral_mul_left_eq_self (μ := μ𝔭(v)) _ a,
    localIdelicZetaIntegral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [Units.val_mul, ← mul_assoc, a.inv_val, one_mul, map_mul]
  ring

/-- Splitting the integer ring into integer units and a dilate of the integer
ring gives the geometric factor without summing an infinite series. -/
private theorem finiteBall_integral (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ)
    (p : (v.adicCompletion F)ˣ) (hp : ‖p.val‖ = (q(v) : ℝ)⁻¹) {s : ℂ} (hs : 0 < s.re) :
    (1 - chart𝔭[v, χ] s p) * localIdelicZetaIntegral μ𝔭(v) (ballTest(v)) (chart𝔭[v, χ] s) =
      ∫ u in U(v), (χ u : ℂ) ∂μ𝔭(v) := by
  classical
  let K := v.adicCompletion F
  let c := chart𝔭[v, χ] s
  let μ := μ𝔭(v)
  let B := ballTest(v)
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : μ.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  have hO (x : K) : x ∈ O(v) ↔ ‖x‖ ≤ 1 := by
    change Valued.v x ≤ 1 ↔ ‖x‖ ≤ 1
    exact (Valued.toNormedField.norm_le_one_iff (x := x)).symm
  have hU (u : Kˣ) : u ∈ U(v) ↔ ‖u.val‖ = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.trans
      Valued.toNormedField.norm_eq_one_iff.symm
  have ho := Submonoid.isOpen_units (Valued.isOpen_valuationSubring K)
  have hk := Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr
    (compactSpace_adicCompletionIntegers v (K := F)))
  let A (u : Kˣ) := (U(v) : Set Kˣ).indicator (fun t ↦ (χ t : ℂ)) u
  have hA : Integrable A μ := (integrable_indicator_iff ho.measurableSet).2
    ((continuous_subtype_val.comp χ.continuous).continuousOn.integrableOn_compact hk)
  obtain ⟨f, hf⟩ := finiteBall_test v
  have hB : Integrable (fun u : Kˣ ↦ B u.val * c u) μ := by
    change Integrable (fun u : Kˣ ↦ ballTest(v) u.val * c u) μ
    rw [← hf]
    exact finiteLocalIdelicZetaIntegral_integrable v f χ hs
  have hd (u : Kˣ) : p.inv * u.val ∈ O(v) ↔ ‖u.val‖ < 1 := by
    rw [hO, Units.inv_eq_val_inv, Units.val_inv_eq_inv_val, norm_mul, norm_inv, ← div_eq_inv_mul,
      div_le_one (norm_pos_iff.mpr p.ne_zero), hp, ← finite_norm_lt_one]
  have heq (u : Kˣ) : B (p.inv * u.val) * c u = B u.val * c u - A u := by
    rcases lt_trichotomy ‖u.val‖ 1 with h | h | h
    · simp only [B, A, one_mul, sub_zero, Set.indicator_of_mem ((hd u).2 h), Set.indicator_of_mem ((hO _).2 h.le),
        Set.indicator_of_notMem (show u ∉ U(v) from fun hu ↦ h.ne ((hU u).1 hu))]
    · have hc : c u = (χ u : ℂ) := by
        change (χ u : ℂ) * ((‖u.val‖ : ℝ) : ℂ) ^ s = _
        rw [h, Complex.ofReal_one, Complex.one_cpow, mul_one]
      simp only [B, A, one_mul, zero_mul, sub_self, Set.indicator_of_notMem (show p.inv * u.val ∉ O(v) from fun hx ↦ h.not_lt ((hd u).1 hx)),
        Set.indicator_of_mem ((hO _).2 h.le), Set.indicator_of_mem ((hU u).2 h), hc]
    · simp only [B, A, zero_mul, sub_self, Set.indicator_of_notMem (show p.inv * u.val ∉ O(v) from fun hx ↦ h.asymm ((hd u).1 hx)),
        Set.indicator_of_notMem (show u.val ∉ O(v) from fun hx ↦ h.not_ge ((hO _).1 hx)),
        Set.indicator_of_notMem (show u ∉ U(v) from fun hx ↦ h.ne' ((hU _).1 hx))]
  have he := finiteZeta_dilate v B c p
  change (∫ u : Kˣ, B (p.inv * u.val) * c u ∂μ) = c p * localIdelicZetaIntegral μ B c at he
  simp_rw [heq] at he
  rw [integral_sub hB hA, show (∫ u, A u ∂μ) = _ from integral_indicator ho.measurableSet] at he
  change localIdelicZetaIntegral μ B c - _ = c p * localIdelicZetaIntegral μ B c at he
  change (1 - c p) * localIdelicZetaIntegral μ B c = _
  linear_combination he

/-- After removing its value at zero times the integer-ring indicator,
a test function has compact support on the multiplicative group. -/
private theorem finite_compact_remainder (v : Primes) (f : ℬ(v.adicCompletion F)) :
    let R (x : v.adicCompletion F) := test(f) x - test(f) 0 * ballTest(v) x
    Continuous R ∧ HasCompactSupport (R ∘ Units.val : (v.adicCompletion F)ˣ → ℂ) := by
  obtain ⟨g, hg⟩ := finiteBall_test v
  have hf := (mem_finitePlaceSchwartz_iff F v test(f)).mp ⟨f, fun _ ↦ rfl⟩
  have hB := (mem_finitePlaceSchwartz_iff F v (ballTest(v))).mp ⟨g, congrFun hg⟩
  let R (x : v.adicCompletion F) := test(f) x - test(f) 0 * ballTest(v) x
  have hR : IsLocallyConstant R := hf.1.comp₂ hB.1 (fun a b ↦ a - test(f) 0 * b)
  have hK : HasCompactSupport R := hf.2.sub hB.2.mul_left
  have hR0 : R 0 = 0 := by simp [R]
  have hs : tsupport R ⊆ range (Units.val : (v.adicCompletion F)ˣ → _) := by
    intro x hx
    have hc : IsClosed (support R) := (hR.isClopen_fiber 0).2.isClosed_compl
    rw [tsupport, hc.closure_eq] at hx
    have hne : x ≠ 0 := by rintro rfl; exact hx hR0
    exact ⟨Units.mk0 x hne, rfl⟩
  have hcomp : IsCompact (Units.val ⁻¹' tsupport R : Set (v.adicCompletion F)ˣ) := by
    rw [(Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).isCompact_iff,
      image_preimage_eq_of_subset hs]
    exact hK
  refine ⟨hR.continuous, hcomp.of_isClosed_subset isClosed_closure ?_⟩
  apply closure_minimal _ (isClosed_closure.preimage Units.continuous_val)
  exact fun u hu ↦ subset_tsupport R hu

/-- The only possible singular part of a finite zeta integral is the geometric
tail from the value of its test function at zero. -/
private theorem finiteZeta_split (v : Primes) (f : ℬ(v.adicCompletion F))
    (χ : PontryaginDual (v.adicCompletion F)ˣ)
    (p : (v.adicCompletion F)ˣ) (hp : ‖p.val‖ = (q(v) : ℝ)⁻¹) :
    ∃ A : ℂ → ℂ, Differentiable ℂ A ∧
      (finiteLocalIdelicZFunction v f ∘ chart𝔭[v, χ]) =ᶠ[codiscrete ℂ] fun s ↦
        A s + test(f) 0 * (∫ u in U(v), (χ u : ℂ) ∂μ𝔭(v)) / (1 - chart𝔭[v, χ] s p) := by
  let K := v.adicCompletion F
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : μ𝔭(v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let R (x : K) := test(f) x - test(f) 0 * ballTest(v) x
  obtain ⟨hc, hK⟩ := finite_compact_remainder v f
  let A (s : ℂ) := localIdelicZetaIntegral μ𝔭(v) R (chart𝔭[v, χ] s)
  have hi (s : ℂ) : Integrable (fun u : Kˣ ↦ R u.val * chart𝔭[v, χ] s u) μ𝔭(v) :=
    ((hc.comp Units.continuous_val).mul (chart𝔭[v, χ] s).continuous).integrable_of_hasCompactSupport
      hK.mul_right
  have hA : Differentiable ℂ A := fun s ↦
    (localIdelicZetaIntegral_analyticAt m𝔭(v) h𝔭(v) μ𝔭(v) R χ (s.re - 1) (fun z _ ↦ hi z) s
      (show s.re - 1 < s.re by linarith)).differentiableAt
  let D (s : ℂ) := 1 - chart𝔭[v, χ] s p
  have hD : Differentiable ℂ D := (differentiable_const _).sub
    ((differentiable_const _).mul (differentiable_id.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr p.ne_zero).ne'))))
  have hq : 1 < (q(v) : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hp0 := norm_pos_iff.mpr p.ne_zero
  have hp1 : ‖p.val‖ < 1 := hp ▸ inv_lt_one_of_one_lt₀ hq
  have hNZ {s : ℂ} (hs : 0 < s.re) : D s ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have h := congrArg norm he
    change ‖(1 : ℂ)‖ = ‖(χ p : ℂ) * ((‖p.val‖ : ℝ) : ℂ) ^ s‖ at h
    rw [norm_one, norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp0] at h
    exact (Real.rpow_lt_one hp0.le hp1 hs).ne' h
  refine ⟨A, hA, meromorphic_eq_of_germ (fun z ↦
    ((finiteLocalIdelicZFunction_existsUnique v f).exists.choose_spec χ).1.meromorphicOn z trivial)
    (fun z ↦ (hA.analyticAt z).meromorphicAt.add ((MeromorphicAt.const _ z).div (hD.analyticAt z).meromorphicAt))
    (z := 1) ?_⟩
  have h₁ : (1 : ℂ) ∈ rightHalf := by norm_num [mem_preimage, mem_Ioi]
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds h₁)] with s hs
  change finiteLocalIdelicZFunction v f (chart𝔭[v, χ] s) = _
  rw [finiteLocalIdelicZFunction_eq_integral v f χ hs]
  obtain ⟨g, hg⟩ := finiteBall_test v
  have hB := finiteLocalIdelicZetaIntegral_integrable v g χ hs
  have hB' : Integrable (fun u : Kˣ ↦ ballTest(v) u.val * chart𝔭[v, χ] s u) μ𝔭(v) := hg ▸ hB
  have he := finiteBall_integral v χ p hp hs
  have hJ : localIdelicZetaIntegral μ𝔭(v) (ballTest(v)) (chart𝔭[v, χ] s) =
      (∫ u in U(v), (χ u : ℂ) ∂μ𝔭(v)) / D s :=
    (eq_div_iff (hNZ hs)).2 ((mul_comm _ _).trans he)
  rw [mul_div_assoc, ← hJ]
  change (∫ u : Kˣ, test(f) u.val * chart𝔭[v, χ] s u ∂μ𝔭(v)) =
    (∫ u : Kˣ, R u.val * chart𝔭[v, χ] s u ∂μ𝔭(v)) +
      test(f) 0 * (∫ u : Kˣ, ballTest(v) u.val * chart𝔭[v, χ] s u ∂μ𝔭(v))
  rw [← integral_const_mul, ← integral_add (hi s) (hB'.const_mul _)]
  apply integral_congr_ae
  filter_upwards with u
  dsimp only [R]
  ring

end FiniteBall

/-- A normalized uniformizer in the completion. -/
private theorem exists_finite_norm_uniformizer (v : Primes) :
    ∃ p : (v.adicCompletion F)ˣ, ‖p.val‖ = (q(v) : ℝ)⁻¹ := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨a, ha⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  exact ⟨Units.mk0 a ha.ne_zero, norm_uniformizer_adicCompletion v _ ha⟩

/-- The geometric denominator has derivative equal to its character value
times the logarithm of the residue cardinality. -/
private theorem finite_den_hasDerivAt (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ)
    (p : (v.adicCompletion F)ˣ) (hp : ‖p.val‖ = (q(v) : ℝ)⁻¹) (s : ℂ) :
    HasDerivAt (fun z ↦ 1 - chart𝔭[v, χ] z p)
      (chart𝔭[v, χ] s p * (Real.log (q(v) : ℝ) : ℂ)) s := by
  let r := ‖p.val‖
  have hr : 0 < r := norm_pos_iff.mpr p.ne_zero
  have hl : Complex.log (r : ℂ) = -(Real.log (q(v) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hr.le, show r = _ from hp, Real.log_inv, Complex.ofReal_neg]
  have hd := ((Complex.hasStrictDerivAt_const_cpow (x := (r : ℂ)) (y := s)
    (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))).hasDerivAt.const_mul (χ p : ℂ)).const_sub 1
  change HasDerivAt (fun z : ℂ ↦ 1 - (χ p : ℂ) * (r : ℂ) ^ z)
    ((χ p : ℂ) * (r : ℂ) ^ s * (Real.log (q(v) : ℝ) : ℂ)) s
  convert hd using 1
  rw [hl]
  ring

section FiniteNormFactor

local notation "N(" v ")" => chart𝔭[v, (1 : PontryaginDual (HeightOneSpectrum.adicCompletion F v)ˣ)]
local notation "B(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v : Set (HeightOneSpectrum.adicCompletion F v)).indicator (fun _ ↦ (1 : ℂ))
local notation "mass(" v ")" => (((μ𝔭(v) (HeightOneSpectrum.adicCompletionIntegers F v).units).toReal : ℝ) : ℂ)

private theorem finite_norm_chart_apply (v : Primes) (z : ℂ) (u : (v.adicCompletion F)ˣ) :
    N(v) z u = ((‖u.val‖ : ℝ) : ℂ) ^ z := by
  change ((1 : Circle) : ℂ) * _ ^ z = _
  simp

/-- The local zeta integral on the integer ball is the Euler factor times
the prescribed multiplicative mass of the integer units. -/
private theorem finiteBall_norm_integral (v : Primes) {s : ℂ} (hs : 0 < s.re) :
    localIdelicZetaIntegral μ𝔭(v) (B(v)) (N(v) s) = mass(v) * finiteLocalEulerFactor v (N(v) s) := by
  obtain ⟨p, hp⟩ := exists_finite_norm_uniformizer v
  have he := finiteBall_integral v 1 p hp hs
  have hq : 1 < (q(v) : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hn : N(v) s p = (q(v) : ℂ) ^ (-s) := by
    rw [finite_norm_chart_apply, hp, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (by positivity),
      ← Complex.cpow_neg, Complex.ofReal_natCast]
  have hNZ : 1 - (q(v) : ℂ) ^ (-s) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have h' := congrArg norm h
    rw [norm_one, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq),
      Complex.neg_re] at h'
    exact (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr hs)).ne' h'
  rw [finiteLocalEulerFactor_norm v hs, ← div_eq_mul_inv]
  apply (eq_div_iff hNZ).mpr
  rw [mul_comm, ← hn, he]
  simp [measureReal_def]

/-- Fourier transformation expands the integer ball by the inverse different.
Its Mellin integral is the corresponding dilation of the integer-ball integral. -/
private theorem finiteFourierBall_norm_integral (v : Primes) {s : ℂ} (hs : 0 < s.re) :
    localIdelicZetaIntegral μ𝔭(v) (F𝔭(v) (B(v))) (N(v) s) =
      mass(v) * (((q(v) : ℂ) ^ diffExp(v)) ^ s) *
        (mass(v) * finiteLocalEulerFactor v (N(v) s)) := by
  obtain ⟨p, hp⟩ := exists_finite_norm_uniformizer v
  let d := diffExp(v)
  let a : (v.adicCompletion F)ˣ := (p ^ d)⁻¹
  have hq : 0 < (q(v) : ℝ) := by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).pos
  have ha : ‖a.val‖ = (q(v) : ℝ) ^ d := by
    simp [a, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_pow, hp]
  have hset : {x : v.adicCompletion F | ‖x‖ ≤ (q(v) : ℝ) ^ d}.indicator (fun _ ↦ (1 : ℂ)) =
      fun x ↦ B(v) (a.inv * x) := by
    funext x
    have he : a.inv * x ∈ (v.adicCompletionIntegers F : Set _) ↔ ‖x‖ ≤ (q(v) : ℝ) ^ d := by
      change Valued.v (a.inv * x) ≤ 1 ↔ _
      rw [← Valued.toNormedField.norm_le_one_iff, Units.inv_eq_val_inv, Units.val_inv_eq_inv_val,
        norm_mul, norm_inv, ← div_eq_inv_mul, div_le_one (norm_pos_iff.mpr a.ne_zero), ha]
    by_cases hx : ‖x‖ ≤ (q(v) : ℝ) ^ d
    · exact (Set.indicator_of_mem hx _).trans (Set.indicator_of_mem (he.mpr hx) (fun _ ↦ (1 : ℂ))).symm
    · exact (Set.indicator_of_notMem hx _).trans (Set.indicator_of_notMem (fun h ↦ hx (he.mp h)) _).symm
  have hchar : N(v) s a = ((q(v) : ℂ) ^ d) ^ s := by
    rw [finite_norm_chart_apply, ha, Complex.ofReal_pow, Complex.ofReal_natCast]
  let M := mass(v)
  have hF : F𝔭(v) (B(v)) = M • (fun x ↦ B(v) (a.inv * x)) := by
    rw [finiteLocalTamagawaFourier_integers, ← hset]
    dsimp only [M]
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits]
  rw [hF]
  have hscale (g : v.adicCompletion F → ℂ) :
      localIdelicZetaIntegral μ𝔭(v) (M • g) (N(v) s) = M * localIdelicZetaIntegral μ𝔭(v) g (N(v) s) := by
    simp only [localIdelicZetaIntegral, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  rw [hscale, finiteZeta_dilate, hchar, finiteBall_norm_integral v hs, mul_assoc]

private theorem finite_mass_eq (v : Primes) :
    mass(v) = ((q(v) : ℂ) ^ diffExp(v)) ^ (-(1 / 2 : ℂ)) := by
  rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_inv, ENNReal.toReal_ofReal
    (Real.sqrt_nonneg _), Complex.ofReal_inv, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity),
    Complex.ofReal_pow, Complex.ofReal_natCast, Complex.cpow_neg]
  norm_num

/-- Paper: Equation (3.3.1.29), p. 135. On a bare norm power the finite
epsilon factor is the different norm to the exponent s minus one half. -/
theorem finiteLocalEpsilonFactor_norm (v : Primes) (s : ℂ) :
    finiteLocalEpsilonFactor v (chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s) =
      ((q(v) : ℂ) ^ diffExp(v)) ^ (s - 1 / 2) := by
  let Q : ℂ := (q(v) : ℂ) ^ diffExp(v)
  let M := mass(v)
  let E (z : ℂ) := finiteLocalEulerFactor v (N(v) z)
  let ρ (z : ℂ) := finiteLocalTateFactor v (N(v) z)
  let H (z : ℂ) := ρ z / E z * E (1 - z)
  let X (z : ℂ) := Q ^ (z - 1 / 2)
  have hq : 1 < (q(v) : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hqC : (q(v) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (HeightOneSpectrum.one_lt_absNorm v).ne_zero
  have hQ : Q ≠ 0 := pow_ne_zero _ hqC
  have hX : Differentiable ℂ X := (differentiable_id.sub_const _).const_cpow (Or.inl hQ)
  have hE : Meromorphic E := by
    have he : E = fun z : ℂ ↦ (1 - (q(v) : ℂ) ^ (-z))⁻¹ := funext fun z ↦ finiteEuler_norm_all v z
    rw [he]
    exact fun z ↦ (((differentiable_const (1 : ℂ)).sub
      (differentiable_neg.const_cpow (Or.inl hqC))).analyticAt z).meromorphicAt.inv
  have hH : Meromorphic H := fun z ↦
    (((finiteLocalTateFactor_spec v).1 1).meromorphicOn z trivial).div (hE z) |>.mul
      ((hE (1 - z)).comp_analyticAt (g := fun t ↦ 1 - t) (by fun_prop))
  have hd (z : ℂ) : dualQuasiCharacter m𝔭(v) h𝔭(v) (N(v) z) = N(v) (1 - z) := by
    have hi : (1 : PontryaginDual (v.adicCompletion F)ˣ)⁻¹ = 1 := by
      ext u
      exact inv_one
    exact (dual_norm_chart m𝔭(v) h𝔭(v) (1 : PontryaginDual (v.adicCompletion F)ˣ) z).trans
      (congrArg (fun χ : PontryaginDual (v.adicCompletion F)ˣ ↦ chart𝔭[v, χ] (1 - z)) hi)
  have hE0 {z : ℂ} (hz : 0 < z.re) : E z ≠ 0 := by
    rw [show E z = _ from finiteEuler_norm_all v z]
    apply inv_ne_zero
    apply sub_ne_zero.mpr
    intro heq
    have h := congrArg norm heq
    rw [norm_one, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq),
      Complex.neg_re] at h
    exact (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr hz)).ne' h
  have heq : H =ᶠ[codiscrete ℂ] X := by
    apply meromorphic_eq_of_germ hH (fun z ↦ (hX.analyticAt z).meromorphicAt) (z := 1 / 2)
    have hstrip : ∀ᶠ z in 𝓝[≠] (1 / 2 : ℂ), z.re ∈ Ioo (0 : ℝ) 1 :=
      nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
        (by norm_num [mem_preimage, mem_Ioo]))
    filter_upwards [hstrip] with z hz
    have hp : 0 < (1 - z).re := by simpa using sub_pos.mpr hz.2
    obtain ⟨f, hf⟩ := finiteBall_test v
    have h := (finiteLocalTateFactor_spec v).2 f 1 z hz
    change localIdelicZetaIntegral μ𝔭(v) test(f) (N(v) z) =
      ρ z * localIdelicZetaIntegral μ𝔭(v) (F𝔭(v) test(f)) _ at h
    rw [hf, hd, finiteFourierBall_norm_integral v hp, finiteBall_norm_integral v hz.1] at h
    change M * E z = ρ z * (M * Q ^ (1 - z) * (M * E (1 - z))) at h
    have hMX : M * Q ^ (1 - z) * X z = 1 := by
      change mass(v) * Q ^ (1 - z) * Q ^ (z - 1 / 2) = 1
      rw [finite_mass_eq]
      change Q ^ (-(1 / 2 : ℂ)) * Q ^ (1 - z) * Q ^ (z - 1 / 2) = 1
      rw [← Complex.cpow_add _ _ hQ, ← Complex.cpow_add _ _ hQ]
      convert Complex.cpow_zero Q using 2
      ring
    have hm : M ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul (hMX.trans_ne one_ne_zero))
    change ρ z / E z * E (1-z) = X z
    rw [div_mul_eq_mul_div, div_eq_iff (hE0 hz.1)]
    apply mul_left_cancel₀ hm
    calc
      M * (ρ z * E (1 - z)) = M * (ρ z * E (1 - z)) * (M * Q ^ (1 - z) * X z) := by rw [hMX, mul_one]
      _ = (ρ z * (M * Q ^ (1 - z) * (M * E (1 - z)))) * X z := by ring
      _ = _ := by rw [← h]; ring
  have ht : finiteLocalEpsilonFactor v (N(v) s) = toMeromorphicNFAt (fun t ↦ H (s + t)) 0 0 := by
    unfold finiteLocalEpsilonFactor
    simp only [norm_chart_twist, hd]
    exact toMeromorphicNFOn_eq_toMeromorphicNFAt
      (fun t _ ↦ (hH (s + t)).comp_analyticAt (g := fun z ↦ s + z) (by fun_prop)) trivial
  rw [ht, normalize_translate_at_zero (fun z _ ↦ hH z) s,
    toMeromorphicNFOn_eq_toMeromorphicNFAt (fun z _ ↦ hH z) trivial,
    (toMeromorphicNFAt_eventuallyEq_nhds_congr (heq.filter_mono (nhdsNE_le_codiscrete s))).eq_of_nhds,
    toMeromorphicNFAt_eq_self.mpr (hX.analyticAt s).meromorphicNFAt]

end FiniteNormFactor

section CongruenceBalls
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

private def congruenceBall (R : ℝ) : Set Kˣ := Units.val ⁻¹' Metric.closedBall 1 R

private theorem mem_congruenceBall {R : ℝ} {u : Kˣ} :
    u ∈ congruenceBall R ↔ ‖u.val-1‖≤R := by
  simp only [congruenceBall,mem_preimage,Metric.mem_closedBall,dist_eq_norm]

private theorem norm_one_of_near_one {u : K} {R : ℝ} (hR : R<1) (hu : ‖u-1‖ ≤ R) : ‖u‖=1 := by
  have ht : ‖u + (-1)‖ < max ‖u‖ ‖(-1:K)‖ := by
    simpa only [norm_neg, norm_one, ← sub_eq_add_neg] using (hu.trans_lt hR).trans_le (le_max_right ‖u‖ 1)
  simpa using IsUltrametricDist.norm_eq_of_add_norm_lt_max ht

private theorem congruenceBall_open {R : ℝ} (hR : 0<R) : IsOpen (congruenceBall (K := K) R) :=
  (IsUltrametricDist.isOpen_closedBall (1:K) hR.ne').preimage Units.continuous_val

private theorem congruenceBall_compact [ProperSpace K] {R : ℝ} (hR : R<1) :
    IsCompact (congruenceBall (K := K) R) := by
  rw [Units.isEmbedding_val₀.isCompact_iff, congruenceBall, image_preimage_eq_of_subset]
  · exact isCompact_closedBall _ _
  · intro x hx
    exact ⟨Units.mk0 x (norm_ne_zero_iff.mp ((norm_one_of_near_one hR (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)).trans_ne one_ne_zero)),rfl⟩

private theorem congruenceBall_coset (a u : Kˣ) {R : ℝ} (ha : ‖a.val‖=1) :
    a⁻¹*u ∈ congruenceBall R ↔ ‖a.val-u.val‖ ≤ R := by
  rw [mem_congruenceBall]
  rw [Units.val_mul, Units.val_inv_eq_inv_val, show a.val⁻¹*u.val-1 = a.val⁻¹*(u.val-a.val) by
    rw [mul_sub, inv_mul_cancel₀ a.ne_zero], norm_mul, norm_inv, ha, inv_one, one_mul, norm_sub_rev]

private theorem congruenceBall_scaled (k u : Kˣ) {R Q : ℝ} (h : ‖k.val‖*R=Q) :
    k⁻¹*u ∈ congruenceBall R ↔ ‖u.val-k.val‖ ≤ Q := by
  rw [mem_congruenceBall]
  rw [Units.val_mul, Units.val_inv_eq_inv_val, show k.val⁻¹*u.val-1 = (u.val-k.val)/k.val by
    field_simp, norm_div, div_le_iff₀ (norm_pos_iff.mpr k.ne_zero), mul_comm R, h]

/-- Integrating a constant on a multiplicative translate of a principal-unit
ball gives the same mass for every representative. -/
private theorem integrate_congruence_coset [MeasurableSpace Kˣ] [BorelSpace Kˣ] (μ : Measure Kˣ)
    [μ.IsMulLeftInvariant] (R : ℝ) (hR : 0<R) (a : Kˣ) (c : ℂ) :
    (∫ u, ((fun u ↦ a⁻¹*u) ⁻¹' congruenceBall R).indicator (fun _ ↦ c) u ∂μ) =
      (μ.real (congruenceBall R):ℂ) * c := by
  have hs : MeasurableSet ((fun u : Kˣ ↦ a⁻¹*u) ⁻¹' congruenceBall R) := ((congruenceBall_open (K := K) hR).preimage ((continuous_const (y := a⁻¹)).mul continuous_id)).measurableSet
  rw [integral_indicator hs, setIntegral_const, measureReal_def, measure_preimage_mul, Complex.real_smul]
  rfl

private theorem integral_eq_zero_of_translate {G : Type*} [CommGroup G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (a : G) (c : ℂ) (hc : c ≠ 1) (f : G → ℂ)
    (hf : ∀ x, f (a*x) = c * f x) : ∫ x, f x ∂μ = 0 := by
  have h := integral_mul_left_eq_self (μ := μ) f a
  simp_rw [hf, integral_const_mul] at h
  exact (mul_eq_zero.mp (show (c-1)*(∫ x, f x ∂μ) = 0 by linear_combination h)).resolve_left (sub_ne_zero.mpr hc)

end CongruenceBalls

section FiniteGauss
local notation "O(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v : Set (HeightOneSpectrum.adicCompletion F v))
local notation "ballTest(" v ")" => (O(v)).indicator (fun _ ↦ (1 : ℂ))
local notation "ψ(" v ")" => (fun x ↦ (finiteLocalStandardCharacter F v x : ℂ))
local notation "Q(" v ")" => ((q(v):ℝ)^diffExp(v))
local notation "M(" v ")" => (((μ𝔭(v) (HeightOneSpectrum.adicCompletionIntegers F v).units).toReal : ℝ) : ℂ)

private theorem finitePhase_sub (v : Primes) (x y : v.adicCompletion F) :
    ψ(v) (x-y) = ψ(v) x / ψ(v) y := by
  obtain ⟨e,he,-⟩ := finiteLocalAdditiveTamagawaMeasure_selfDual F v
  let φ := e (Multiplicative.ofAdd 1)
  have h (t : v.adicCompletion F) : φ (Multiplicative.ofAdd t) = finiteLocalStandardCharacter F v t := by
    simpa only [one_mul] using he 1 t
  change (finiteLocalStandardCharacter F v (x-y) : ℂ) = (finiteLocalStandardCharacter F v x : ℂ) / (finiteLocalStandardCharacter F v y : ℂ)
  simp only [← h, show Multiplicative.ofAdd (x-y) = Multiplicative.ofAdd x / Multiplicative.ofAdd y from rfl,
    map_div, Circle.coe_div]

private theorem finitePhase_eq (v : Primes) {x y : v.adicCompletion F} (h : ‖x-y‖ ≤ Q(v)) :
    ψ(v) x = ψ(v) y := by
  have hm : x-y ∈ {z : v.adicCompletion F | ‖z‖ ≤ Q(v)} := h
  rw [← finiteLocalStandardCharacter_annihilator_integers F v] at hm
  have h1 := hm 1 (v.adicCompletionIntegers F).one_mem
  rw [one_mul] at h1
  apply (div_eq_one_iff_eq (Circle.coe_ne_zero _)).mp
  rw [← finitePhase_sub]
  exact congrArg ((↑) : Circle → ℂ) h1

private theorem finitePhase_localConst (v : Primes) (k : (v.adicCompletion F)ˣ) :
    IsLocallyConstant (fun x : v.adicCompletion F ↦ ψ(v) (k.val*x)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hq : 0 < (q(v):ℝ) := by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).pos
  have hk := norm_pos_iff.mpr k.ne_zero
  filter_upwards [Metric.ball_mem_nhds x (div_pos (pow_pos hq _) hk)] with y hy
  apply finitePhase_eq
  rw [← mul_sub, norm_mul, mul_comm, ← le_div_iff₀ hk]
  exact (show ‖y-x‖ < _ from hy).le

private theorem finiteGauss_test (v : Primes) (k : (v.adicCompletion F)ˣ) :
    ∃ f : ℬ(v.adicCompletion F), test(f) = (fun x ↦ ballTest(v) x * ψ(v) (k.val*x)) ∧
      F𝔭(v) test(f) = fun y ↦ M(v) * ({x : v.adicCompletion F | ‖x-k.val‖ ≤ Q(v)}.indicator (fun _ ↦ (1:ℂ)) y) := by
  obtain ⟨b,hb⟩ := finiteBall_test v
  obtain ⟨hLC,hK⟩ := (mem_finitePlaceSchwartz_iff F v (ballTest(v))).mp ⟨b,congrFun hb⟩
  obtain ⟨f,hf⟩ := (mem_finitePlaceSchwartz_iff F v (fun x ↦ ballTest(v) x * ψ(v) (k.val*x))).mpr ⟨hLC.mul (finitePhase_localConst v k), hK.mul_right⟩
  have hf' := funext hf
  refine ⟨f,hf',funext fun y ↦ ?_⟩
  have he : F𝔭(v) test(f) y = F𝔭(v) (ballTest(v)) (y-k.val) := by
    change (∫ x, test(f) x * star (ψ(v) (x*y)) ∂_) = ∫ x, ballTest(v) x * star (ψ(v) (x*(y-k.val))) ∂_
    apply integral_congr_ae
    filter_upwards with x
    have hi (t : v.adicCompletion F) : star (ψ(v) t) = (ψ(v) t)⁻¹ :=
      (Circle.coe_inv_eq_conj _).symm
    rw [hf x, mul_sub, mul_comm k.val x]
    have hsub : (finiteLocalStandardCharacter F v (x*y-x*k.val) : ℂ) = ψ(v) (x*y) / ψ(v) (x*k.val) := finitePhase_sub v _ _
    rw [hsub, star_div₀, hi (x*y), hi (x*k.val)]
    simp only [div_eq_mul_inv,inv_inv]
    ring
  rw [he, finiteLocalTamagawaFourier_integers]
  have hM := finiteLocalMultiplicativeTamagawaMeasure_integerUnits F v
  change _ = ((μ𝔭(v) (HeightOneSpectrum.adicCompletionIntegers F v).units).toReal : ℂ) * _
  rw [hM]
  by_cases hy : ‖y-k.val‖ ≤ Q(v) <;> simp [hy]


private theorem finiteGauss_integral (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ)
    (k : (v.adicCompletion F)ˣ) (R : ℝ) (hR₀ : 0<R) (hR₁ : R<1) (hk : ‖k.val‖*R=Q(v))
    (hχ : ∀ u ∈ congruenceBall (K := v.adicCompletion F) R, χ u = 1)
    (a : (v.adicCompletion F)ˣ) (ha : ‖a.val‖=1) (hχa : χ a ≠ 1)
    (hkill : ‖k.val‖*‖a.val-1‖*(q(v):ℝ)⁻¹ ≤ Q(v))
    (U : Finset ((v.adicCompletion F)ˣ)) (hU : ∀ u ∈ U, ‖u.val‖=1)
    (hreps : ∀ u : (v.adicCompletion F)ˣ, ‖u.val‖=1 → ∃! j : U, ‖j.val.val-u.val‖ ≤ R)
    (s : ℂ) (hs : 0<s.re) :
    localIdelicZetaIntegral μ𝔭(v) (fun x ↦ ballTest(v) x * ψ(v) (k.val*x)) (chart𝔭[v,χ] s) =
      (μ𝔭(v).real (congruenceBall R):ℂ) * ∑ j ∈ U, (χ j : ℂ)*ψ(v) (k.val*j.val) := by
  classical
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace Kˣ := ⟨rfl⟩
  let μ := μ𝔭(v)
  let : μ.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let c := chart𝔭[v,χ] s
  let h (u : Kˣ) := ballTest(v) u.val * ψ(v) (k.val*u.val) * c u
  let W := {u : Kˣ | ‖u.val‖ < 1}
  let P := congruenceBall (K := K) R
  let D (j : Kˣ) := (fun u ↦ j⁻¹*u) ⁻¹' P
  let coef (j : Kˣ) := (χ j : ℂ) * ψ(v) (k.val*j.val)
  have hO (x : K) : x ∈ O(v) ↔ ‖x‖ ≤ 1 := by
    change Valued.v x ≤ 1 ↔ ‖x‖ ≤ 1
    exact (Valued.toNormedField.norm_le_one_iff (x := x)).symm
  have hc (u : Kˣ) (hu : ‖u.val‖=1) : c u = (χ u : ℂ) := by
    change (χ u : ℂ) * (‖u.val‖ : ℂ)^s = _
    simp [hu]
  have hi : Integrable h μ := by
    obtain ⟨f,hf,-⟩ := finiteGauss_test v k
    exact (finiteLocalIdelicZetaIntegral_integrable v f χ hs).congr (.of_forall fun u ↦
      congrArg (· * c u) (congrFun hf u.val))
  have hW : MeasurableSet W := (isOpen_lt (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet
  have hzero : (∫ u in W, h u ∂μ) = 0 := by
    rw [← integral_indicator hW]
    apply integral_eq_zero_of_translate μ a (χ a : ℂ) (fun e ↦ hχa (Subtype.ext e))
    intro u
    have hn : ‖(a*u).val‖ = ‖u.val‖ := by rw [Units.val_mul, norm_mul,ha,one_mul]
    by_cases hu : u ∈ W
    · have hau : a*u ∈ W := hn.trans_lt hu
      have hphase : ψ(v) (k.val*(a*u).val) = ψ(v) (k.val*u.val) := by
        apply finitePhase_eq
        rw [Units.val_mul, show k.val*(a.val*u.val)-k.val*u.val = k.val*(a.val-1)*u.val by ring, norm_mul,norm_mul]
        exact (mul_le_mul_of_nonneg_left ((finite_norm_lt_one v u).mp hu) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans hkill
      have ho : u.val ∈ O(v) := (hO _).mpr (le_of_lt (show ‖u.val‖<1 from hu))
      have hao : (a*u).val ∈ O(v) := (hO _).mpr (hn ▸ (hO _).mp ho)
      simp only [indicator_of_mem hu, indicator_of_mem hau,h,indicator_of_mem ho,indicator_of_mem hao,
        one_mul,hphase,map_mul,hc a ha]
      ring
    · have hau : a*u ∉ W := fun hf ↦ hu (hn.symm.trans_lt hf)
      simp [indicator_of_notMem hu,indicator_of_notMem hau]
  have hDm (j : Kˣ) : MeasurableSet (D j) :=
    ((congruenceBall_open (K := K) hR₀).preimage (continuous_const.mul continuous_id)).measurableSet
  have hDf (j : Kˣ) : μ (D j) ≠ ⊤ := by
    change μ ((fun u ↦ j⁻¹*u) ⁻¹' P) ≠ ⊤
    rw [measure_preimage_mul]
    exact (congruenceBall_compact (K := K) hR₁).measure_lt_top.ne
  have hche (j u : Kˣ) (hj : ‖j.val‖=1) (hu : u ∈ D j) : ‖u.val‖=1 ∧ h u=coef j := by
    have hp : j⁻¹*u ∈ congruenceBall R := hu
    have hnorm := norm_one_of_near_one hR₁ (mem_congruenceBall.mp hp)
    rw [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, hj, inv_one, one_mul] at hnorm
    have hξ : χ u = χ j := by
      have hh := hχ _ hp
      rw [map_mul,map_inv,inv_mul_eq_one] at hh
      exact hh.symm
    have hphase : ψ(v) (k.val*u.val) = ψ(v) (k.val*j.val) := by
      apply finitePhase_eq
      rw [← mul_sub,norm_mul,norm_sub_rev]
      exact (mul_le_mul_of_nonneg_left ((congruenceBall_coset j u hj).mp hu) (norm_nonneg _)).trans_eq hk
    refine ⟨hnorm,?_⟩
    simp only [h,coef,indicator_of_mem ((hO _).mpr hnorm.le),one_mul,hphase,hc _ hnorm,hξ,mul_comm]
  have hdec (u : Kˣ) : Wᶜ.indicator h u = ∑ j ∈ U, (D j).indicator (fun _ ↦ coef j) u := by
    by_cases hu : ‖u.val‖=1
    · obtain ⟨⟨j,hj⟩,hju,hunique⟩ := hreps u hu
      have hdj : u ∈ D j := (congruenceBall_coset j u (hU _ hj)).mpr hju
      rw [Finset.sum_eq_single_of_mem j hj, indicator_of_mem hdj,
        indicator_of_mem (show u ∈ Wᶜ from fun h ↦ hu.not_lt h)]
      · exact (hche _ _ (hU _ hj) hdj).2
      · intro i hi hij
        apply indicator_of_notMem
        exact fun hd ↦ hij (congrArg Subtype.val (hunique ⟨i,hi⟩ ((congruenceBall_coset i u (hU _ hi)).mp hd)))
    · rw [Finset.sum_eq_zero (fun j hj ↦ indicator_of_notMem (fun hd ↦ hu (hche j u (hU _ hj) hd).1) _)]
      by_cases hlt : ‖u.val‖<1
      · exact indicator_of_notMem ((show u ∉ Wᶜ from fun hcomp ↦ hcomp hlt)) _
      · have hnot : u.val ∉ O(v) := fun ho ↦ hu (le_antisymm ((hO _).mp ho) (not_lt.mp hlt))
        rw [indicator_of_mem (show u ∈ Wᶜ from hlt)]
        simp [h,indicator_of_notMem hnot]
  change (∫ u, h u ∂μ) = _
  rw [← integral_add_compl hW hi, hzero, zero_add, ← integral_indicator hW.compl]
  simp_rw [hdec]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ integrate_congruence_coset μ R hR₀ j (coef j)
  · exact fun j _ ↦ (integrableOn_const (hDf j)).integrable_indicator (hDm j)


private theorem finiteGauss_dualIntegral (v : Primes) (k : (v.adicCompletion F)ˣ) (R : ℝ)
    (hR : 0<R) (hk : ‖k.val‖*R=Q(v)) (c : QuasiCharacter (v.adicCompletion F)ˣ)
    (hc : ∀ u ∈ congruenceBall (K := v.adicCompletion F) R, c u=1) :
    localIdelicZetaIntegral μ𝔭(v) (fun y ↦ M(v) *
      ({x : v.adicCompletion F | ‖x-k.val‖≤Q(v)}.indicator (fun _ ↦ (1:ℂ)) y)) c =
      M(v) * c k * (μ𝔭(v).real (congruenceBall R):ℂ) := by
  let K := v.adicCompletion F
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : μ𝔭(v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let P := congruenceBall (K := K) R
  rw [localIdelicZetaIntegral, ← integral_mul_left_eq_self (μ := μ𝔭(v)) _ k]
  have he (u : Kˣ) : k*u ∈ (fun t : Kˣ ↦ ‖t.val-k.val‖) ⁻¹' Iic Q(v) ↔ u ∈ P := by
    change ‖(k*u).val-k.val‖≤Q(v) ↔ u ∈ P
    simpa only [inv_mul_cancel_left] using (congruenceBall_scaled k (k*u) hk).symm
  have hv (u : Kˣ) : M(v) * ({x : K | ‖x-k.val‖≤Q(v)}.indicator (fun _ ↦ (1:ℂ)) (k*u).val) * c (k*u) =
      P.indicator (fun _ ↦ M(v) * c k) u := by
    by_cases hu : u ∈ P
    · have hmem : (k*u).val ∈ {x : K | ‖x-k.val‖≤Q(v)} := (he u).mpr hu
      simp only [indicator_of_mem hu, indicator_of_mem hmem, map_mul, hc _ hu, mul_one]
    · have hmem : (k*u).val ∉ {x : K | ‖x-k.val‖≤Q(v)} := fun h ↦ hu ((he u).mp h)
      simp only [indicator_of_notMem hu, indicator_of_notMem hmem, mul_zero, zero_mul]
  change (∫ u, _ ∂_) = _
  rw [integral_congr_ae (.of_forall hv)]
  rw [integral_indicator (congruenceBall_open hR).measurableSet, setIntegral_const, Complex.real_smul]
  ring

private theorem ramifiedEuler_one (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ)
    (a : (v.adicCompletion F)ˣ) (ha : ‖a.val‖=1) (hχa : χ a ≠ 1) (z : ℂ) :
    finiteLocalEulerFactor v (chart𝔭[v,χ] z)=1 ∧ finiteLocalEulerFactor v
      (dualQuasiCharacter m𝔭(v) h𝔭(v) (chart𝔭[v,χ] z))=1 := by
  let O := v.adicCompletionIntegers F
  have hmem (x : v.adicCompletion F) : x ∈ O ↔ ‖x‖ ≤ 1 := by
    change Valued.v x ≤ 1 ↔ ‖x‖ ≤ 1
    exact (Valued.toNormedField.norm_le_one_iff (x := x)).symm
  let u : Oˣ := ⟨⟨a.val,(hmem _).mpr ha.le⟩,⟨a.inv,(hmem _).mpr (by
    rw [Units.inv_eq_val_inv, Units.val_inv_eq_inv_val, norm_inv,ha,inv_one])⟩,Subtype.ext a.val_inv,Subtype.ext a.inv_val⟩
  let c := chart𝔭[v,χ] z
  have hcu : c a = (χ a : ℂ) := by change (χ a : ℂ) * (‖a.val‖:ℂ)^z = _; simp [ha]
  have hdu : dualQuasiCharacter m𝔭(v) h𝔭(v) c a = (χ a : ℂ)⁻¹ := by
    change (‖a.val‖:ℂ) * c a⁻¹ = _
    simp [ha,map_inv,hcu]
  have hu : Units.map O.subtype.toMonoidHom u = a := Units.ext rfl
  have hn : (χ a : ℂ) ≠ 1 := fun h ↦ hχa (Subtype.ext h)
  constructor
  · apply ite_eq_right
    intro h
    exact hn (hcu.symm.trans (hu ▸ h u))
  · apply ite_eq_right
    intro h
    exact hn (inv_eq_one.mp (hdu.symm.trans (hu ▸ h u)))

private theorem ramifiedEpsilon_of_strip (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ)
    (a : (v.adicCompletion F)ˣ) (ha : ‖a.val‖=1) (hχa : χ a ≠ 1)
    (X : ℂ → ℂ) (hX : Differentiable ℂ X)
    (h : ∀ s : ℂ, s.re ∈ Ioo (0:ℝ) 1 → finiteLocalTateFactor v (chart𝔭[v,χ] s) = X s) (s : ℂ) :
    finiteLocalEpsilonFactor v (chart𝔭[v,χ] s) = X s := by
  let ρ (z : ℂ) := finiteLocalTateFactor v (chart𝔭[v,χ] z)
  have hρ := (finiteLocalTateFactor_spec v).1 χ
  have hh : ρ =ᶠ[codiscrete ℂ] X := by
    apply meromorphic_eq_of_germ (fun z ↦ hρ.meromorphicOn z trivial) (fun z ↦ (hX.analyticAt z).meromorphicAt)
      (z := 1/2)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
      (show (1/2:ℂ) ∈ Complex.re ⁻¹' Ioo (0:ℝ) 1 by norm_num [mem_preimage,mem_Ioo]))] with z hz
    exact h z hz
  have he (z : ℂ) : ρ z = X z := ((hρ (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hX.analyticAt z).meromorphicNFAt).mp (hh.filter_mono (nhdsNE_le_codiscrete z)) |>.eq_of_nhds
  have hE := ramifiedEuler_one v χ a ha hχa
  unfold finiteLocalEpsilonFactor
  simp only [norm_chart_twist,(hE _).1,(hE _).2,div_one,mul_one]
  change toMeromorphicNFOn (fun t ↦ ρ (s+t)) univ 0 = _
  simp_rw [he]
  have hn : MeromorphicNFOn (fun t ↦ X (s+t)) univ := fun t _ ↦ ((hX.analyticAt (s+t)).comp (f := fun z : ℂ ↦ s+z) (by fun_prop)).meromorphicNFAt
  rw [toMeromorphicNFOn_eq_self.mpr hn]
  simp


/-- Paper: Equation (3.3.1.30), p. 136. For a ramified unitary base trivial
on the chosen uniformizer, the epsilon factor is the normalized Gauss sum
over unit representatives modulo the conductor times the indicated norm power.
Deviation: The norm power uses the product of the different and conductor.
The sum uses the existing finite standard character, including the sign in F13. -/
theorem finiteLocalEpsilonFactor_ramified (v : Primes)
    (χ : PontryaginDual (v.adicCompletion F)ˣ) (π : (v.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer (π : v.adicCompletion F)) (hχπ : χ π = 1)
    (n : ℕ) (hn : 0 < n)
    (hcond : IsLeast {j : ℕ | ∀ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 →
      ‖u.val - 1‖ ≤ (q(v) : ℝ) ^ (-(j : ℤ)) → χ u = 1} n)
    (U : Finset ((v.adicCompletion F)ˣ)) (hU : ∀ u ∈ U, ‖u.val‖ = 1)
    (hreps : ∀ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 →
      ∃! a : U, ‖a.val.val - u.val‖ ≤ (q(v) : ℝ) ^ (-(n : ℤ))) (s : ℂ) :
    finiteLocalEpsilonFactor v (chart𝔭[v, χ] s) =
      ((q(v) : ℂ) ^ (diffExp(v) + n)) ^ (s - 1 / 2) *
        ((q(v) : ℂ) ^ n) ^ (-(1 / 2 : ℂ)) *
        ∑ u ∈ U, (χ u : ℂ) *
          (finiteLocalStandardCharacter F v (u.val / π.val ^ (diffExp(v) + n)) : ℂ) :=
  by
  classical
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : μ𝔭(v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let q : ℝ := q(v)
  let d := diffExp(v)
  let n := j+1
  let k : Kˣ := (π^(d+n))⁻¹
  let R := q ^ (-(n:ℤ))
  let A : ℂ := (q:ℂ)^(d+n)
  let B : ℂ := (q:ℂ)^n
  let C := ∑ u ∈ U, (χ u : ℂ)*ψ(v) (k.val*u.val)
  let Y (z : ℂ) := A^(z-1/2)*B^(-(1/2:ℂ))
  have hq : 1 < q := by dsimp [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq' : 0 < q := zero_lt_one.trans hq
  have hA : A ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hq'.ne')
  have hnorm : ‖k.val‖ = q^(d+n) := by
    simp [k, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_pow,
      norm_uniformizer_adicCompletion v _ hπ, q]
  have hR : 0 < R := zpow_pos hq' _
  have hR' : R < 1 := by
    rw [show R = (q^n)⁻¹ by simp [R]]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
  have hk : ‖k.val‖*R=Q(v) := by
    rw [hnorm, show R = (q^n)⁻¹ by simp [R],pow_add,mul_inv_cancel_right₀ (pow_ne_zero _ hq'.ne')]
  have hχ (u : Kˣ) (hu : u ∈ congruenceBall R) : χ u = 1 :=
    hcond.1 u (norm_one_of_near_one hR' (mem_congruenceBall.mp hu)) (mem_congruenceBall.mp hu)
  have hnot : ¬ ∀ u : Kˣ, ‖u.val‖=1 → ‖u.val-1‖ ≤ q^(-(j:ℤ)) → χ u=1 :=
    fun hh ↦ (Nat.not_succ_le_self j) (hcond.2 hh)
  push Not at hnot
  obtain ⟨a,ha,hclose,hχa⟩ := hnot
  have hkill : ‖k.val‖*‖a.val-1‖*q⁻¹ ≤ Q(v) := by
    calc
      _ ≤ ‖k.val‖*(q^(-(j:ℤ)))*q⁻¹ := by gcongr
      _ = ‖k.val‖*R := by
        rw [show R = (q^(j+1))⁻¹ by rw [show R = q^(-(n:ℤ)) from rfl,zpow_neg,zpow_natCast], zpow_neg, zpow_natCast, pow_succ, mul_inv, mul_assoc]
      _ = _ := hk
  have hχk : χ k = 1 := by simp [k,hχπ]
  have hC : C = ∑ u ∈ U, (χ u : ℂ) * ψ(v) (u.val / π.val ^ (d+n)) := by
    apply Finset.sum_congr rfl
    intro u _
    rw [show k.val * u.val = u.val / π.val^(d+n) by simp [k, div_eq_mul_inv, mul_comm]]
  change _ = Y s * _
  rw [← hC]
  apply ramifiedEpsilon_of_strip v χ a ha hχa (fun z ↦ Y z*C)
    (((differentiable_id.sub_const _).const_cpow (Or.inl hA) |>.mul_const _).mul_const _)
  intro z hz
  let δ := dualQuasiCharacter m𝔭(v) h𝔭(v) (chart𝔭[v,χ] z)
  have hd (u : Kˣ) : δ u = ((χ u : ℂ)⁻¹) * (‖u.val‖:ℂ)^(1-z) := by
    rw [show δ = chart𝔭[v,χ⁻¹] (1-z) from dual_norm_chart _ _ _ _]
    rfl
  have hdP (u : Kˣ) (hu : u ∈ congruenceBall R) : δ u=1 := by
    rw [hd,hχ u hu,norm_one_of_near_one hR' (mem_congruenceBall.mp hu)]
    simp
  have hdk : δ k = A^(1-z) := by
    rw [hd,hχk,hnorm,Complex.ofReal_pow]
    simp [A]
  let V : ℂ := μ𝔭(v).real (congruenceBall R)
  have hV : V ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (ENNReal.toReal_pos ((congruenceBall_open hR).measure_pos μ𝔭(v)
      ⟨1,mem_congruenceBall.mpr (by simpa using hR.le)⟩).ne' (congruenceBall_compact hR').measure_lt_top.ne).ne'
  obtain ⟨f,hf,hF⟩ := finiteGauss_test v k
  have h := (finiteLocalTateFactor_spec v).2 f χ z hz
  change localIdelicZetaIntegral μ𝔭(v) test(f) _ = _ * localIdelicZetaIntegral μ𝔭(v) (F𝔭(v) test(f)) δ at h
  rw [hF,hf,finiteGauss_integral v χ k R hR hR' hk hχ a ha hχa hkill U hU hreps z hz.1,
    finiteGauss_dualIntegral v k R hR hk δ hdP,hdk] at h
  have hYP : M(v) * A^(1-z) * Y z = 1 := by
    let D : ℂ := (q:ℂ)^d
    have hD : D ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hq'.ne')
    have hB : B ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hq'.ne')
    have hspl : A^(1/2:ℂ) = D^(1/2:ℂ)*B^(1/2:ℂ) := by
      simpa only [A,D,B,Complex.ofReal_pow,pow_add,Complex.ofReal_mul] using
        Complex.mul_cpow_ofReal_nonneg (pow_nonneg hq'.le d) (pow_nonneg hq'.le n) (1/2:ℂ)
    rw [finite_mass_eq]
    change D^(-(1/2:ℂ))*A^(1-z)*(A^(z-1/2)*B^(-(1/2:ℂ))) = 1
    rw [mul_assoc, ← mul_assoc (A^(1-z)), ← Complex.cpow_add _ _ hA,
      show (1-z)+(z-1/2) = 1/2 by ring, hspl,Complex.cpow_neg,Complex.cpow_neg]
    field_simp [Complex.cpow_ne_zero_iff.mpr (Or.inl hD), Complex.cpow_ne_zero_iff.mpr (Or.inl hB)]
  change V*C = finiteLocalTateFactor v _ * (M(v)*A^(1-z)*V) at h
  apply mul_right_cancel₀ hV
  calc
    _ = (finiteLocalTateFactor v (chart𝔭[v,χ] z) * (M(v)*A^(1-z)*V))*Y z := by
      conv_lhs => rw [← mul_one (finiteLocalTateFactor v _), ← hYP]
      ring
    _ = Y z*C*V := by rw [← h]; ring

end FiniteGauss

/-- A nontrivial local character detects some uniformizer. Multiplication
by any integer unit preserves the set of uniformizers. -/
private theorem finite_select_uniformizer (v : Primes) (c : QuasiCharacter (v.adicCompletion F)ˣ)
    (hc : c ≠ 1) :
    ∃ p : (v.adicCompletion F)ˣ, ‖p.val‖ = (q(v) : ℝ)⁻¹ ∧ c p ≠ 1 := by
  by_contra! h
  apply hc
  obtain ⟨p, hp⟩ := exists_finite_norm_uniformizer v
  obtain ⟨e, hep, heι⟩ := finitePlace_unitDecomposition v p hp
  let ι := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom
  have hi (u : (v.adicCompletionIntegers F)ˣ) : c (ι u) = 1 := by
    have hu : ‖(ι u).val‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
      ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := ι u)).mp
        ⟨u.val.prop, u.inv.prop⟩)
    have hpu := h (p * ι u) (by rw [Units.val_mul, norm_mul, hu, mul_one, hp])
    rwa [map_mul, h p hp, one_mul] at hpu
  ext1 x
  have hx : x = p ^ (e x).1.toAdd * ι (e x).2 := by
    apply e.injective
    rw [map_mul, map_zpow, hep, heι]
    exact Prod.ext (by change (e x).1.toAdd = (e x).1.toAdd * 1 + 0; simp) (by simp)
  rw [hx, map_mul, map_zpow, h p hp, hi, one_zpow, one_mul]
  rfl

/-- Away from the trivial character one can choose a uniformizer at which
the geometric denominator is nonzero. -/
private theorem finiteZeta_regular (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ)
    (s : ℂ) (hc : chart𝔭[v, χ] s ≠ 1) (f : ℬ(v.adicCompletion F)) :
    0 ≤ meromorphicOrderAt (finiteLocalIdelicZFunction v f ∘ chart𝔭[v, χ]) s := by
  obtain ⟨p, hp, hcp⟩ := finite_select_uniformizer v _ hc
  obtain ⟨A, hA, he⟩ := finiteZeta_split v f χ p hp
  have hD : Differentiable ℂ (fun z ↦ 1 - chart𝔭[v, χ] z p) := fun z ↦
    (finite_den_hasDerivAt v χ p hp z).differentiableAt
  rw [meromorphicOrderAt_congr (he.filter_mono (nhdsNE_le_codiscrete s))]
  exact ((hA.analyticAt s).add (analyticAt_const.div (hD.analyticAt s)
    (sub_ne_zero.mpr hcp.symm))).meromorphicOrderAt_nonneg

/-- At a point representing the trivial character, the unit angular integral
is the positive mass of the integer units. -/
private theorem finite_unit_integral_ne_zero (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ)
    (s : ℂ) (hs : chart𝔭[v, χ] s = 1) :
    (∫ u in (v.adicCompletionIntegers F).units, (χ u : ℂ) ∂μ𝔭(v)) ≠ 0 := by
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let U := (v.adicCompletionIntegers F).units
  have ho : IsOpen (U : Set (v.adicCompletion F)ˣ) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring (v.adicCompletion F))
  have hk : IsCompact (U : Set (v.adicCompletion F)ˣ) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  let : μ𝔭(v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  have hm : 0 < μ𝔭(v) (U : Set (v.adicCompletion F)ˣ) := ho.measure_pos _ ⟨1, U.one_mem⟩
  have he : (∫ u in (U : Set (v.adicCompletion F)ˣ), (χ u : ℂ) ∂μ𝔭(v)) =
      ∫ _ in (U : Set (v.adicCompletion F)ˣ), (1 : ℂ) ∂μ𝔭(v) := by
    apply setIntegral_congr_fun ho.measurableSet
    intro u hu
    have hn : ‖u.val‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu)
    have hval := DFunLike.congr_fun hs u
    change (χ u : ℂ) * ((‖u.val‖ : ℝ) : ℂ) ^ s = 1 at hval
    simpa only [hn, Complex.ofReal_one, Complex.one_cpow, mul_one] using hval
  change (∫ u in (U : Set (v.adicCompletion F)ˣ), (χ u : ℂ) ∂μ𝔭(v)) ≠ 0
  rw [he, setIntegral_const, Complex.real_smul, mul_one]
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hm.ne' hk.measure_lt_top.ne).ne'

/-- Paper: Lemma 3.3.2.2, p. 141. Each scalar finite local zeta function
has at most simple poles. A pole occurs for some test function exactly over
the trivial quasi-character, including its periodic lifts in the exponent plane.
Deviation: Tests against Schwartz–Bruhat functions specify the distributional pole. -/
theorem finiteLocalIdelicZFunction_poles (v : Primes)
    (χ : PontryaginDual (v.adicCompletion F)ˣ) (s : ℂ) :
    (∀ f : ℬ(v.adicCompletion F),
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (finiteLocalIdelicZFunction v f ∘ chart𝔭[v, χ]) s) ∧
    ((∃ f : ℬ(v.adicCompletion F),
      meromorphicOrderAt (finiteLocalIdelicZFunction v f ∘ chart𝔭[v, χ]) s = -1) ↔
      chart𝔭[v, χ] s = 1) := by
  classical
  let c := chart𝔭[v, χ] s
  by_cases hc : c = 1
  · obtain ⟨p, hp⟩ := exists_finite_norm_uniformizer v
    let D (z : ℂ) := 1 - chart𝔭[v, χ] z p
    have hD : Differentiable ℂ D := fun z ↦ (finite_den_hasDerivAt v χ p hp z).differentiableAt
    have hcp : chart𝔭[v, χ] s p = 1 := DFunLike.congr_fun hc p
    have hq : 1 < (q(v) : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    have hd : deriv D s ≠ 0 := by
      rw [show deriv D s = _ from (finite_den_hasDerivAt v χ p hp s).deriv, hcp, one_mul]
      exact Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
    have hord : meromorphicOrderAt D s = 1 := by
      rw [(hD.analyticAt s).meromorphicOrderAt_eq,
        (hD.analyticAt s).analyticOrderAt_eq_one_of_zero_deriv_ne_zero (sub_eq_zero.mpr hcp.symm) hd]
      rfl
    let M := ∫ u in (v.adicCompletionIntegers F).units, (χ u : ℂ) ∂μ𝔭(v)
    have hM : M ≠ 0 := finite_unit_integral_ne_zero v χ s hc
    have horder (a : ℂ) (ha : a ≠ 0) :
        meromorphicOrderAt (fun z ↦ a / D z) s = -1 := by
      change meromorphicOrderAt ((fun _ ↦ a) / D) s = -1
      rw [meromorphicOrderAt_div (MeromorphicAt.const a s) (hD.analyticAt s).meromorphicAt,
        meromorphicOrderAt_const, ite_eq_right ha, hord]
      rfl
    have htest (f : ℬ(v.adicCompletion F)) :
        if test(f) 0 = 0 then 0 ≤ meromorphicOrderAt (finiteLocalIdelicZFunction v f ∘ chart𝔭[v, χ]) s
        else meromorphicOrderAt (finiteLocalIdelicZFunction v f ∘ chart𝔭[v, χ]) s = -1 := by
      obtain ⟨A, hA, he⟩ := finiteZeta_split v f χ p hp
      rw [meromorphicOrderAt_congr (he.filter_mono (nhdsNE_le_codiscrete s))]
      have hAnon := (hA.analyticAt s).meromorphicOrderAt_nonneg
      split_ifs with hf
      · simpa only [hf, zero_mul, zero_div, add_zero] using hAnon
      · let g (z : ℂ) := (test(f) 0 * M) / D z
        have hg : meromorphicOrderAt g s = -1 := horder _ (mul_ne_zero hf hM)
        change meromorphicOrderAt (A + g) s = -1
        exact (meromorphicOrderAt_add_eq_right_of_lt (hA.analyticAt s).meromorphicAt
          (hg ▸ (show (-1 : WithTop ℤ) < 0 by decide).trans_le hAnon)).trans hg
    refine ⟨fun f ↦ ?_, ⟨fun _ ↦ hc, fun _ ↦ ?_⟩⟩
    · have h := htest f
      split_ifs at h
      · exact (show (-1 : WithTop ℤ) ≤ 0 by decide).trans h
      · exact h.ge
    · obtain ⟨f, hf⟩ := finiteBall_test v
      refine ⟨f, ?_⟩
      have h := htest f
      have h0 : test(f) 0 ≠ 0 := by rw [hf]; simp
      simpa only [ite_eq_right h0] using h
  · have hreg := finiteZeta_regular v χ s hc
    refine ⟨fun f ↦ (show (-1 : WithTop ℤ) ≤ 0 by decide).trans (hreg f), ?_⟩
    exact ⟨fun ⟨f, hf⟩ ↦ absurd (hf ▸ hreg f) (by decide), fun h ↦ (hc h).elim⟩

-- TODO(paper-gap): In (3.3.2.23) the indicator of ℤₚˣ would have nonzero
-- residue, but its trivial-component zeta integral is identically 1.
-- The measure relation used under (3.3.2.25) omits the finite-place factor
-- q/(q−1) of Lemma A.3.2.3.

/-- Paper: Equation (3.3.2.23), p. 141. The residue at the trivial character
is evaluation at zero times the multiplicative mass of the integer units
divided by log of the residue field size.
Deviation: Fourier inversion yields f(0). The factor 1−q⁻¹ cancels against
the weighted measure factor in Lemma A.3.2.3. -/
theorem finiteLocalIdelicZFunction_residue (v : Primes) (f : ℬ(v.adicCompletion F)) :
    Tendsto (fun s : ℂ ↦ s * finiteLocalIdelicZFunction v f
      (chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s)) (𝓝[≠] 0)
      (𝓝 (((μ𝔭(v) (v.adicCompletionIntegers F).units).toReal : ℂ) /
        (Real.log (q(v) : ℝ) : ℂ) * test(f) 0)) := by
  obtain ⟨p, hp⟩ := exists_finite_norm_uniformizer v
  let χ : PontryaginDual (v.adicCompletion F)ˣ := 1
  let D (z : ℂ) := 1 - chart𝔭[v, χ] z p
  let L : ℂ := Real.log (q(v) : ℝ)
  let M : ℂ := (μ𝔭(v) (v.adicCompletionIntegers F).units).toReal
  have hM : (∫ u in (v.adicCompletionIntegers F).units, (χ u : ℂ) ∂μ𝔭(v)) = M := by
    simp [χ, M, measureReal_def]
  have hc : chart𝔭[v, χ] 0 p = 1 := by
    change ((1 : Circle) : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hD : HasDerivAt D L 0 := by simpa only [hc, one_mul] using finite_den_hasDerivAt v χ p hp 0
  have hq : 1 < (q(v) : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hL : L ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  have hlim : Tendsto (fun s ↦ s / D s) (𝓝[≠] 0) (𝓝 L⁻¹) := by
    have he : D 0 = 0 := sub_eq_zero.mpr hc.symm
    simpa only [slope_def_field, he, sub_zero, inv_div] using hD.tendsto_slope.inv₀ hL
  obtain ⟨A, hA, heq⟩ := finiteZeta_split v f χ p hp
  have ht : Tendsto (fun s : ℂ ↦ s * A s) (𝓝[≠] 0) (𝓝 (0 * A 0)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).mul
    ((hA.continuous.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds)
  have hsum := ht.add (hlim.const_mul (test(f) 0 * M))
  have hval : 0 * A 0 + test(f) 0 * M * L⁻¹ = M / L * test(f) 0 := by ring
  rw [hval] at hsum
  apply hsum.congr'
  · filter_upwards [heq.filter_mono (nhdsNE_le_codiscrete 0)] with s hs
    change s * A s + test(f) 0 * M * (s / D s) = s * finiteLocalIdelicZFunction v f (chart𝔭[v, χ] s)
    change finiteLocalIdelicZFunction v f (chart𝔭[v, χ] s) = A s + _ / D s at hs
    rw [hs, hM]
    ring


/-- Paper: §3.3.2, p. 137. In each finite-place chart the local zeta function
is meromorphic with values in the strong dual of the test space.
Deviation: Agreement with scalar normal form is required off the
distributional poles. -/
theorem finiteLocalIdelicZFunction_distribution (v : Primes)
    (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    let poles := {s : ℂ | chart𝔭[v, χ] s = 1}
    ∃ Z : ℂ → StrongDual ℂ (ℬ(v.adicCompletion F)), IsVectorMeromorphicOn Z univ poles ∧
      ∀ s ∉ poles, ∀ f, Z s f = finiteLocalIdelicZFunction v f (chart𝔭[v, χ] s) := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let : μ𝔭(v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let : (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have he : {s : ℂ | ∃ f, meromorphicOrderAt (finiteLocalIdelicZFunction v f ∘ chart𝔭[v,χ]) s < 0} =
      {s : ℂ | chart𝔭[v,χ] s = 1} := by
    ext s
    constructor
    · rintro ⟨f,hf⟩
      exact Classical.byContradiction fun h ↦ hf.not_ge (finiteZeta_regular v χ s h f)
    · intro hs
      obtain ⟨f,hf⟩ := (finiteLocalIdelicZFunction_poles v χ s).2.mpr hs
      exact ⟨f, hf ▸ (by decide : (-1 : WithTop ℤ) < 0)⟩
  let P : Set ℂ := {s | ∃ f, meromorphicOrderAt (finiteLocalIdelicZFunction v f ∘ chart𝔭[v,χ]) s < 0}
  let Q : Set ℂ := {s | chart𝔭[v,χ] s = 1}
  have h (A : Set ℂ) (hA : P = A) : ∃ Z : ℂ → StrongDual ℂ (ℬ(v.adicCompletion F)),
      IsVectorMeromorphicOn Z univ A ∧ ∀ s ∉ A, ∀ f, Z s f = finiteLocalIdelicZFunction v f (chart𝔭[v,χ] s) := by
    subst A
    exact localZeta_distribution m𝔭(v) h𝔭(v) μ𝔭(v) _ _ (finiteLocalAdditiveTamagawaMeasure_selfDual F v)
      _ (finiteLocalTateFactor_spec v) (finiteLocalIdelicZFunction v)
      (fun f η ↦ (finiteLocalIdelicZFunction_existsUnique v f).exists.choose_spec η)
      (fun f η _ hz ↦ finiteLocalIdelicZetaIntegral_integrable v f η hz) χ
  exact h Q he


section RamifiedRegularity

local notation "unitchar(" χ ")" => ((circleToComplex).comp χ)
local notation "N(" v ")" => chart𝔭[v, (1 : PontryaginDual (HeightOneSpectrum.adicCompletion F v)ˣ)]

private theorem finite_integer_unit_norm (v : Primes) (u : (v.adicCompletionIntegers F)ˣ) :
    ‖(Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u : (v.adicCompletion F)ˣ).val‖ = 1 :=
  Valued.toNormedField.norm_eq_one_iff.mpr
    ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u)).mp ⟨u.val.prop, u.inv.prop⟩)

/-- A character trivial on the integer units is a complex power of the local norm. -/
private theorem finite_unramified_is_norm (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ)
    (hχ : unramified[v, unitchar(χ)]) :
    ∃ t : ℂ, ∀ s, chart𝔭[v, χ] s = N(v) (t + s) := by
  obtain ⟨p, hp⟩ := exists_finite_norm_uniformizer v
  obtain ⟨e, hep, heι⟩ := finitePlace_unitDecomposition v p hp
  let ι := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom
  let r := ‖p.val‖
  have hr : 0 < r := norm_pos_iff.mpr p.ne_zero
  have hq : 1 < (q(v) : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hlt : r < 1 := by change ‖p.val‖ < 1; rw [hp]; exact inv_lt_one_of_one_lt₀ hq
  have hL : Complex.log (r : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_log hr.le]
    exact Complex.ofReal_ne_zero.mpr (Real.log_neg hr hlt).ne
  let t := Complex.log (χ p : ℂ) / Complex.log (r : ℂ)
  have htp : N(v) t p = (χ p : ℂ) := by
    rw [finite_norm_chart_apply, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')]
    change Complex.exp (Complex.log (r : ℂ) * (Complex.log (χ p : ℂ) / Complex.log (r : ℂ))) = _
    rw [mul_div_cancel₀ _ hL, Complex.exp_log (Circle.coe_ne_zero _)]
  have heq : unitchar(χ) = N(v) t := by
    ext1 x
    have hx : x = p ^ (e x).1.toAdd * ι (e x).2 := by
      apply e.injective
      rw [map_mul, map_zpow, hep, heι]
      exact Prod.ext (by change (e x).1.toAdd = (e x).1.toAdd * 1 + 0; simp) (by simp)
    have htu (u : (v.adicCompletionIntegers F)ˣ) : N(v) t (ι u) = 1 := by
      rw [finite_norm_chart_apply, finite_integer_unit_norm v u, Complex.ofReal_one, Complex.one_cpow]
    rw [hx, map_mul, map_mul, map_zpow, map_zpow, hχ, htu, htp]
    rfl
  exact ⟨t, fun s ↦ (congrArg (fun c ↦ quasiCharacterNormTwist m𝔭(v) h𝔭(v) c s) heq).trans
    (norm_chart_twist m𝔭(v) h𝔭(v) 1 t s)⟩

/-- A compact open subgroup of the integer units kills the unitary character,
so its indicator has constant positive Mellin integral along the chart. -/
private theorem exists_finite_constant_zeta_test (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    ∃ (g : ℬ(v.adicCompletion F)) (C : ℂ), C ≠ 0 ∧
      ∀ z, localIdelicZetaIntegral μ𝔭(v) test(g) (chart𝔭[v, χ] z) = C := by
  classical
  let K := v.adicCompletion F
  let U := (v.adicCompletionIntegers F).units
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : ProperSpace K := properSpace_adicCompletion v
  let : LocallyCompactSpace Kˣ := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).locallyCompactSpace
  let : TotallyDisconnectedSpace Kˣ := (Units.isEmbedding_val₀ (G₀ := K)).isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  let : μ𝔭(v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let ξ := unitchar(χ)
  have ho : IsOpen (U : Set Kˣ) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring K)
  have hball : ξ ⁻¹' Metric.ball (1 : ℂ) 1 ∈ 𝓝 1 := ξ.continuous.continuousAt.preimage_mem_nhds
    (by change Metric.ball (1 : ℂ) 1 ∈ 𝓝 (ξ 1); rw [map_one]; exact Metric.ball_mem_nhds _ zero_lt_one)
  obtain ⟨H, hK, hsub⟩ := exists_compact_openSubgroup_sub_mem_nhds
    (inter_mem (ho.mem_nhds U.one_mem) hball)
  let : CompactSpace H := isCompact_iff_compactSpace.mp hK
  let φ := ξ.toMonoidHom.comp H.toSubgroup.subtype
  have hφ : φ = 1 := monoidHom_eq_one_of_compact_range_subset_ball φ
    (isCompact_range (ξ.continuous.comp continuous_subtype_val)) (by
      rintro _ ⟨u, rfl⟩
      exact (hsub u.prop).2)
  let V := Units.val '' (H : Set Kˣ)
  have hV : IsCompact V := hK.image Units.continuous_val
  have hcl : IsClopen V := ⟨hV.isClosed, (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).isOpenMap _ H.isOpen⟩
  obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v (V.indicator (fun _ ↦ (1 : ℂ)))).2
    ⟨(LocallyConstant.charFn ℂ hcl).isLocallyConstant, hV.of_isClosed_subset isClosed_closure
      (closure_minimal support_indicator_subset hcl.1)⟩
  refine ⟨g, ((μ𝔭(v) (H : Set Kˣ)).toReal : ℂ), Complex.ofReal_ne_zero.mpr
    (ENNReal.toReal_pos (H.isOpen.measure_pos _ ⟨1, H.one_mem⟩).ne' hK.measure_lt_top.ne).ne', fun z ↦ ?_⟩
  rw [show test(g) = _ from funext hg]
  apply localIdelicZetaIntegral_indicator _ _ _ H.isOpen.measurableSet hK.measure_lt_top.ne
  intro u hu
  have hn : ‖u.val‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp (hsub hu).1)
  have hξ : (χ u : ℂ) = 1 := DFunLike.congr_fun hφ (⟨u, hu⟩ : H)
  change (χ u : ℂ) * ((‖u.val‖ : ℝ) : ℂ) ^ z = 1
  rw [hn, Complex.ofReal_one, Complex.one_cpow, hξ, one_mul]

/-- Every finite-place test function has a test function as its inverse Fourier transform. -/
private theorem exists_finite_inverseFourier (v : Primes) (g : ℬ(v.adicCompletion F)) :
    ∃ f : ℬ(v.adicCompletion F), F𝔭(v) test(f) = test(g) := by
  let K := v.adicCompletion F
  let G := Multiplicative K
  let ν := finiteLocalAdditiveTamagawaMeasure F v
  let μ : Measure G := ν
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace G := ⟨rfl⟩
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace K)
  have hν := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hν.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hν.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hν.map_add_left_eq_self x.toAdd }
  let : BorelSpace K := ⟨rfl⟩
  let : μ.Regular := addHaar_regular_of_sigmaCompactSpace ν
  obtain ⟨e, he, -⟩ := finiteLocalAdditiveTamagawaMeasure_selfDual F v
  obtain ⟨T, hT⟩ := schwartzBruhat_fourier_equiv μ
  let g' : SchwartzBruhat (PontryaginDual G) :=
    ⟨g.val ∘ e.symm, schwartzBruhat_mem_comp_equiv e.symm g.property⟩
  let f := T.symm g'
  refine ⟨f, funext fun y ↦ ?_⟩
  rw [tamagawaFourier_eq_lcaFourier _ _ _ y (e (Multiplicative.ofAdd y)) (fun x ↦ by
    rw [mul_comm x y]
    exact he y x)]
  exact ((hT f).2 _).symm.trans ((congrArg (fun u : SchwartzBruhat (PontryaginDual G) ↦ u (e (Multiplicative.ofAdd y))) (T.apply_symm_apply g')).trans (congrArg g (e.symm_apply_apply _)))

/-- Paper: Lemma 3.3.1.7(3)(a), p. 135. The finite local epsilon factor
is entire in each norm-twist chart. -/
theorem finiteLocalEpsilonFactor_entire (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    AnalyticOnNhd ℂ (finiteLocalEpsilonFactor v ∘ chart𝔭[v, χ]) univ := by
  by_cases hun : unramified[v, unitchar(χ)]
  · obtain ⟨t, ht⟩ := finite_unramified_is_norm v χ hun
    have hq : (q(v) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (HeightOneSpectrum.one_lt_absNorm v).ne_zero
    have hA : Differentiable ℂ (fun s : ℂ ↦ ((q(v) : ℂ) ^ diffExp(v)) ^ (t + s - 1 / 2)) :=
      ((differentiable_id.const_add _).sub_const _).const_cpow (Or.inl (pow_ne_zero _ hq))
    intro s _
    apply (hA.analyticAt s).congr
    exact .of_forall fun z ↦ (ht z ▸ finiteLocalEpsilonFactor_norm v (t + z)).symm
  · let Z := finiteLocalIdelicZFunction v
    let ρ (z : ℂ) := finiteLocalTateFactor v (chart𝔭[v, χ] z)
    have hρ := (finiteLocalTateFactor_spec v).1 χ
    obtain ⟨g, C, hC, hg⟩ := exists_finite_constant_zeta_test v χ⁻¹
    obtain ⟨f, hf⟩ := exists_finite_inverseFourier v g
    have hZ := ((finiteLocalIdelicZFunction_existsUnique v f).exists.choose_spec χ).1
    have hE (z : ℂ) : finiteLocalEulerFactor v (chart𝔭[v, χ] z) = 1 ∧
        finiteLocalEulerFactor v (dualQuasiCharacter m𝔭(v) h𝔭(v) (chart𝔭[v, χ] z)) = 1 ∧
        chart𝔭[v, χ] z ≠ 1 := by
      push Not at hun
      obtain ⟨u, hu⟩ := hun
      let x := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
      have hn := finite_integer_unit_norm v u
      have hx : chart𝔭[v, χ] z x = (χ x : ℂ) := by
        change (χ x : ℂ) * ((‖x.val‖ : ℝ) : ℂ) ^ z = _
        rw [hn, Complex.ofReal_one, Complex.one_cpow, mul_one]
      have hdx : dualQuasiCharacter m𝔭(v) h𝔭(v) (chart𝔭[v, χ] z) x = (χ x : ℂ)⁻¹ := by
        change ((‖x.val‖ : ℝ) : ℂ) * chart𝔭[v, χ] z x⁻¹ = _
        rw [hn, Complex.ofReal_one, one_mul, map_inv, hx]
      have hn₁ : ¬ unramified[v, chart𝔭[v, χ] z] := fun h ↦ hu (hx.symm.trans (h u))
      have hn₂ : ¬ unramified[v, dualQuasiCharacter m𝔭(v) h𝔭(v) (chart𝔭[v, χ] z)] :=
        fun h ↦ hu (inv_eq_one.mp (hdx.symm.trans (h u)))
      exact ⟨ite_eq_right hn₁, ite_eq_right hn₂, fun h ↦ hu (hx.symm.trans (DFunLike.congr_fun h x))⟩
    have hreg (z : ℂ) : AnalyticAt ℂ (Z f ∘ chart𝔭[v, χ]) z := by
      apply (hZ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      exact finiteZeta_regular v χ z (hE z).2.2 f
    have heq : ρ =ᶠ[codiscrete ℂ] fun z ↦ Z f (chart𝔭[v, χ] z) / C := by
      apply meromorphic_eq_of_germ (fun z ↦ hρ.meromorphicOn z trivial)
        (fun z ↦ (hreg z).meromorphicAt.div (MeromorphicAt.const _ _)) (z := 1 / 2)
      have hstrip : ∀ᶠ z in 𝓝[≠] (1 / 2 : ℂ), z.re ∈ Ioo (0 : ℝ) 1 :=
        nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
          (by norm_num [mem_preimage, mem_Ioo]))
      filter_upwards [hstrip] with z hz
      apply (eq_div_iff hC).mpr
      have ht := (finiteLocalTateFactor_spec v).2 f χ z hz
      change localIdelicZetaIntegral μ𝔭(v) test(f) _ = ρ z * localIdelicZetaIntegral μ𝔭(v)
        (F𝔭(v) test(f)) _ at ht
      rw [hf, dual_norm_chart] at ht
      exact ((congrArg (ρ z * ·) (hg (1 - z))).symm.trans ht.symm).trans (finiteLocalIdelicZFunction_eq_integral v f χ hz.1).symm
    have hρA (z : ℂ) : AnalyticAt ℂ ρ z :=
      ((hreg z).div analyticAt_const hC).congr
        (((hρ (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
          ((hreg z).div analyticAt_const hC).meromorphicNFAt).mp
          (heq.filter_mono (nhdsNE_le_codiscrete z))).symm
    have hval (s : ℂ) : finiteLocalEpsilonFactor v (chart𝔭[v, χ] s) = ρ s := by
      unfold finiteLocalEpsilonFactor
      simp only [norm_chart_twist, (hE _).1, (hE _).2.1, div_one, mul_one]
      have ha : AnalyticOnNhd ℂ (fun t ↦ ρ (s + t)) univ := fun t _ ↦
        (hρA (s + t)).comp (f := fun t ↦ s + t) (by fun_prop)
      rw [toMeromorphicNFOn_eq_self.mpr (fun t _ ↦ (ha t trivial).meromorphicNFAt)]
      simp
    intro z _
    exact (hρA z).congr (.of_forall fun s ↦ (hval s).symm)

end RamifiedRegularity

private theorem sLocalInfinite_charts (χ : PontryaginDual Jₛ) (w : InfinitePlace F) :
    ∃ η : PontryaginDual w.Completionˣ, (∀ z, sLocalInfiniteRestriction w (chartₛ(χ) z) = chart∞[w,η] z) ∧
      ∀ z, sLocalInfiniteRestriction w (dualQuasiCharacter (G := Jₛ) mₛ hmₛ (chartₛ(χ) z)) =
        dualQuasiCharacter m∞(w) h∞(w) (chart∞[w,η] z) := by
  let h := sLocalInfiniteInsertion_properties (S := S) w
  let i : w.Completionˣ →ₜ* Jₛ :=
    ⟨{ toFun := fun g ↦ QuotientGroup.mk (sInfiniteUnit(w, g)),
       map_one' := h.1, map_mul' := h.2.1 }, h.2.2⟩
  have hm (g : w.Completionˣ) :
      (((mₛ (i g) : ℝ≥0) : ℝ) : ℂ) = (((m∞(w) g : ℝ≥0) : ℝ) : ℂ) := by
    have he := sLocalInfiniteRestriction_norm (S := S) w g
    change ((1 : PontryaginDual Jₛ) (i g) : ℂ) *
      (((mₛ (i g) : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at he
    simpa only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] using he
  have hchart (s : ℂ) : sLocalInfiniteRestriction w (chartₛ(χ) s) = chart∞[w, (χ.comp i)] s := by
    ext1 g
    exact congrArg (fun z : ℂ ↦ (χ (i g) : ℂ) * z ^ s) (hm g)
  refine ⟨χ.comp i,hchart,fun z ↦ ContinuousMonoidHom.ext fun g ↦ ?_⟩
  change ((((mₛ (i g) : ℝ≥0):ℝ)):ℂ) * chartₛ(χ) z (i g)⁻¹ =
    ((((m∞(w) g : ℝ≥0):ℝ)):ℂ) * chart∞[w,χ.comp i] z g⁻¹
  rw [hm]
  apply congrArg (_ * ·)
  exact (congrArg (fun u : Jₛ ↦ chartₛ(χ) z u) (show (i g)⁻¹ = i g⁻¹ from (map_inv i g).symm)).trans
    (DFunLike.congr_fun (hchart z) g⁻¹)

private theorem sLocalFinite_charts (χ : PontryaginDual Jₛ) (v : S) :
    ∃ η : PontryaginDual (v.val.adicCompletion F)ˣ, (∀ z, sLocalFiniteRestriction v (chartₛ(χ) z) = chart𝔭[v.val,η] z) ∧
      ∀ z, sLocalFiniteRestriction v (dualQuasiCharacter (G := Jₛ) mₛ hmₛ (chartₛ(χ) z)) =
        dualQuasiCharacter m𝔭(v.val) h𝔭(v.val) (chart𝔭[v.val,η] z) := by
  let h := sLocalFiniteInsertion_properties v
  let i : (v.val.adicCompletion F)ˣ →ₜ* Jₛ :=
    ⟨{ toFun := fun g ↦ QuotientGroup.mk (sFiniteUnit(v, g)),
       map_one' := h.1, map_mul' := h.2.1 }, h.2.2⟩
  have hm (g : (v.val.adicCompletion F)ˣ) :
      (((mₛ (i g) : ℝ≥0) : ℝ) : ℂ) = (((m𝔭(v.val) g : ℝ≥0) : ℝ) : ℂ) := by
    have he := sLocalFiniteRestriction_norm v g
    change ((1 : PontryaginDual Jₛ) (i g) : ℂ) *
      (((mₛ (i g) : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at he
    simpa only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] using he
  have hchart (s : ℂ) : sLocalFiniteRestriction v (chartₛ(χ) s) = chart𝔭[v.val, (χ.comp i)] s := by
    ext1 g
    exact congrArg (fun z : ℂ ↦ (χ (i g) : ℂ) * z ^ s) (hm g)
  refine ⟨χ.comp i,hchart,fun z ↦ ContinuousMonoidHom.ext fun g ↦ ?_⟩
  change ((((mₛ (i g) : ℝ≥0):ℝ)):ℂ) * chartₛ(χ) z (i g)⁻¹ =
    ((((m𝔭(v.val) g : ℝ≥0):ℝ)):ℂ) * chart𝔭[v.val,χ.comp i] z g⁻¹
  rw [hm]
  apply congrArg (_ * ·)
  exact (congrArg (fun u : Jₛ ↦ chartₛ(χ) z u) (show (i g)⁻¹ = i g⁻¹ from (map_inv i g).symm)).trans
    (DFunLike.congr_fun (hchart z) g⁻¹)

/-- A finite-place restriction of a unitary norm-twist chart and its dual is a local chart and its dual. -/
alias sLocalFiniteRestriction_exists_normTwistChart := sLocalFinite_charts

/-- Paper: Lemma 3.3.1.7(3)(b), p. 136. The S-local epsilon factor is entire. -/
theorem sLocalEpsilonFactor_entire (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalEpsilonFactor (chartₛ(χ) s)) univ := by
  have hArch (w : InfinitePlace F) : Differentiable ℂ
      (fun s ↦ infiniteLocalEpsilonFactor w (sLocalInfiniteRestriction w (chartₛ(χ) s))) := by
    obtain ⟨η, h, _⟩ := sLocalInfinite_charts χ w
    simp_rw [h]
    exact fun s ↦ ((infiniteLocalEpsilonFactor_entire w η) s trivial).differentiableAt
  have hFin (v : S) : Differentiable ℂ
      (fun s ↦ finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) s))) := by
    obtain ⟨η, h, _⟩ := sLocalFinite_charts χ v
    simp_rw [h]
    exact fun s ↦ ((finiteLocalEpsilonFactor_entire v.val η) s trivial).differentiableAt
  exact fun s _ ↦ ((Differentiable.fun_finsetProd (fun w _ ↦ hArch w)).mul
    (Differentiable.fun_finsetProd (fun v _ ↦ hFin v))).analyticAt s

/-- Duality in the norm-twist chart takes the inverse unitary character and
reflects the exponent. -/
private theorem sLocal_dual_chart (χ : PontryaginDual Jₛ) (s : ℂ) :
    dualQuasiCharacter (G := Jₛ) mₛ hmₛ (chartₛ(χ) s) = chartₛ(χ⁻¹) (1 - s) :=
  dual_norm_chart mₛ hmₛ χ s

section HarmonicGaussian
open scoped FourierTransform ComplexConjugate
local notation "Sc" => SchwartzMap ℂ ℂ
private def orientedCoord (h : Bool) : ℂ →L[ℝ] ℂ :=
  if h then Complex.conjCLE.toContinuousLinearMap else ContinuousLinearMap.id ℝ ℂ
private theorem orientedCoord_one (h : Bool) : orientedCoord h 1 = 1 := by cases h <;> simp [orientedCoord]
private theorem orientedCoord_I_sq (h : Bool) : (orientedCoord h Complex.I)^2 = -1 := by
  cases h <;> simp [orientedCoord]
private theorem orientedCoord_eq (h : Bool) (z : ℂ) :
    (z.re : ℂ)+orientedCoord h Complex.I*(z.im:ℂ) = orientedCoord h z := by
  conv_rhs => rw [← Complex.re_add_im z]
  cases h <;> simp [orientedCoord,mul_comm]

/-- Duality sends a unitary norm-twist chart to the inverse unitary chart at the reflected parameter. -/
alias sLocalNormTwistChart_dual := sLocal_dual_chart

private def modelGaussian {E : Type*} [SeminormedAddCommGroup E] (b : ℝ) (z : E) : ℂ :=
  Real.exp (-b * ‖z‖^2)

private theorem modelGaussian_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : ℝ) (z u : E) : fderiv ℝ (modelGaussian b) z u =
      (-2*b:ℝ) * (inner ℝ z u : ℝ) * modelGaussian b z := by
  let D := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (-b)
  have H := Complex.ofRealCLM.hasFDerivAt.comp z D.exp
  change fderiv ℝ (Complex.ofRealCLM ∘ fun z : E ↦ Real.exp (-b*‖z‖^2)) z u = _
  rw [H.fderiv]
  simp [modelGaussian,Complex.real_smul,innerSL_apply_apply]
  ring

private theorem orientedGaussian_deriv (b : ℝ) (h : Bool) (n : ℕ) (z u : ℂ) :
    let f := fun t ↦ (orientedCoord h t)^n * modelGaussian b t
    fderiv ℝ f z u = (n:ℂ)*(orientedCoord h z)^(n-1)*orientedCoord h u*modelGaussian b z +
      (orientedCoord h z)^n * ((-2*b:ℝ)*(inner ℝ z u : ℝ)*modelGaussian b z) := by
  let W := orientedCoord h
  have hG : DifferentiableAt ℝ (modelGaussian b) z :=
    (Complex.ofRealCLM.hasFDerivAt.comp z ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (-b)).exp).differentiableAt
  have hp := (W.hasFDerivAt.pow n).mul hG.hasFDerivAt
  change fderiv ℝ ((fun t ↦ W t ^ n) * modelGaussian b) z u = _
  rw [hp.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,
    modelGaussian_deriv,nsmul_eq_mul,W]
  ring

private theorem complexInner_one (z : ℂ) : inner ℝ z 1 = z.re := by
  rw [real_inner_eq_re_inner ℂ]
  simp [RCLike.inner_apply]
private theorem complexInner_I (z : ℂ) : inner ℝ z Complex.I = z.im := by
  rw [real_inner_eq_re_inner ℂ]
  simp [RCLike.inner_apply]

private theorem coordD_fourier (u : ℂ) (f : Sc) (z : ℂ) :
    𝓕 (coordD u f) z = (2*Real.pi*Complex.I) * (inner ℝ z u:ℝ) * 𝓕 f z := by
  change 𝓕 (LineDeriv.lineDerivOp u f) z = _
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp only [smul_apply,SchwartzMap.smulLeftCLM_apply_apply (Function.hasTemperateGrowth_inner_left u),
    Complex.real_smul,smul_eq_mul,mul_assoc]

/-- Multiplying by a holomorphic or antiholomorphic monomial carries a
Gaussian to a harmonic oscillator eigenfunction. The two partial derivatives
in the indicated combination annihilate the monomial. -/
private theorem exists_harmonicGaussian (b : ℝ) (hb : 0<b) (h : Bool) (n : ℕ) :
    ∃ f : Sc, (∀ z, f z = (orientedCoord h z)^n * modelGaussian b z) ∧
      ∀ z, 𝓕 f z = ((-Real.pi:ℂ)*Complex.I/b)^n * (orientedCoord h z)^n *
        𝓕 (modelGaussian b : ℂ → ℂ) z := by
  induction n with
  | zero =>
    obtain ⟨g,hg⟩ := exists_gaussian_schwartz (E := ℂ) b hb
    refine ⟨g, fun z ↦ by simpa [modelGaussian] using hg z, fun z ↦ ?_⟩
    simp only [pow_zero,one_mul,SchwartzMap.fourier_coe]
    exact congrFun (congrArg (fun f : ℂ → ℂ ↦ 𝓕 f) (funext hg)) z
  | succ n ih =>
    obtain ⟨f,hf,hF⟩ := ih
    let e := orientedCoord h Complex.I
    let g : Sc := ((-2*(b:ℂ))⁻¹) • (coordD 1 f + e • coordD Complex.I f)
    have hB : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
    have he : e^2 = -1 := orientedCoord_I_sq h
    refine ⟨g, fun z ↦ ?_, fun z ↦ ?_⟩
    · change _ * (coordD 1 f z + e * coordD Complex.I f z) = _
      simp only [coordD_apply,funext hf,orientedGaussian_deriv,orientedCoord_one,complexInner_one,complexInner_I]
      change _ * (_ + e * (_ * e * _ + _)) = _
      rw [pow_succ]
      rw [← orientedCoord_eq h z]
      change _ = _ * ((z.re:ℂ)+e*(z.im:ℂ)) * _
      push_cast
      generalize (↑z.re + orientedCoord h Complex.I * ↑z.im : ℂ) ^ (n-1) = P
      generalize (↑z.re + orientedCoord h Complex.I * ↑z.im : ℂ) ^ n = Q
      field_simp [hB]
      linear_combination (-((n:ℂ)*P*modelGaussian b z)) * he
    · simp only [g,FourierTransform.fourier_smul,FourierTransform.fourier_add,
        smul_apply,add_apply,smul_eq_mul,coordD_fourier,
        complexInner_one,complexInner_I,hF,pow_succ]
      rw [← orientedCoord_eq h z]
      dsimp only [e]
      field_simp

end HarmonicGaussian

section GaussianMellin
open scoped FourierTransform

private theorem realGaussian_integral (w : InfinitePlace F) (hw : w.IsReal)
    (g : SchwartzMap ℝ ℂ) (c : QuasiCharacter w.Completionˣ) (z : ℂ) (a : Fin 2)
    (hc : realShape[hw,c,z,a]) (hz : 0<z.re)
    (hg : ∀ t : ℝ, g t = (t:ℂ)^a.val * (Real.exp (-Real.pi*t^2):ℂ)) :
    localIdelicZetaIntegral μ∞(w) (fun x ↦ g (realModel(hw) x)) c =
      Complex.Gammaℝ (z+a.val) := by
  rw [realIntegral_shape w hw g c z a hc hz]
  have he : (fun t : ℝ ↦ g t + (-1:ℂ)^a.val*g (-t)) = fun t : ℝ ↦ (2:ℂ) •
      ((t:ℂ)^a.val*(Real.exp (-Real.pi*t^2):ℂ)) := by
    funext t
    fin_cases a <;> simp [hg,smul_eq_mul] <;> ring
  rw [he,mellin_const_smul,mellin_weightedGaussian _ Real.pi_pos _ _ hz,Complex.Gammaℝ_def,smul_eq_mul]
  rw [neg_div]
  ring

private theorem oriented_angular (r : ℤ) (t θ : ℝ) :
    (orientedCoord (decide (0≤r)) ((t:ℂ)*angularWeight 1 θ))^r.natAbs *
      angularWeight r θ = (t:ℂ)^r.natAbs := by
  have hp (n : ℕ) : (angularWeight 1 θ)^n = angularWeight (n:ℤ) θ := by
    simp only [angularWeight,Int.cast_one,one_mul,Int.cast_natCast,←Complex.exp_nat_mul]
    congr 1
    ring
  cases r with
  | ofNat n =>
    change (star ((t:ℂ)*angularWeight 1 θ))^n * angularWeight (n:ℤ) θ = _
    have ht : star (t:ℂ) = (t:ℂ) := Complex.conj_ofReal _
    rw [star_mul,ht,mul_comm (star _),mul_pow,← star_pow,hp,←angularWeight_neg,mul_assoc,← angularWeight_add,neg_add_cancel]
    simp [angularWeight]
  | negSucc n =>
    change ((t:ℂ)*angularWeight 1 θ)^(n+1)*angularWeight (Int.negSucc n) θ = _
    rw [mul_pow,hp,mul_assoc,←angularWeight_add,show ((n+1:ℕ):ℤ)+Int.negSucc n=0 by omega]
    simp [angularWeight]

private theorem complexGaussian_integral (w : InfinitePlace F) (hw : w.IsComplex)
    (g : SchwartzMap ℂ ℂ) (c : QuasiCharacter w.Completionˣ) (z : ℂ) (r : ℤ)
    (hc : complexShape[hw,c,z,r]) (hz : 0<z.re)
    (hg : ∀ t : ℂ, g t = (orientedCoord (decide (0≤r)) t)^r.natAbs *
      (Real.exp (-(2*Real.pi)*‖t‖^2):ℂ)) :
    localIdelicZetaIntegral μ∞(w) (fun x ↦ g (complexModel(hw) x)) c =
      (Real.pi:ℂ) * Complex.Gammaℂ (z+r.natAbs/2) := by
  rw [complexIntegral_shape w hw g c z r hc hz]
  have he : angularProfile g r = fun t : ℝ ↦ (2*(Real.pi:ℂ)) •
      ((t:ℂ)^r.natAbs*(Real.exp (-(2*Real.pi)*t^2):ℂ)) := by
    funext t
    have h (θ : ℝ) : angularWeight r θ*g ((t:ℂ)*angularWeight 1 θ) =
        (t:ℂ)^r.natAbs*(Real.exp (-(2*Real.pi)*t^2):ℂ) := by
      rw [hg,norm_mul,angularWeight_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,sq_abs,
        ←oriented_angular r t θ]
      ring
    unfold angularProfile
    simp_rw [h]
    simp [Complex.real_smul,two_mul,max_eq_left (add_nonneg Real.pi_pos.le Real.pi_pos.le)]
  rw [he,mellin_const_smul,mellin_weightedGaussian _ (by positivity) _ _ (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hz),Complex.Gammaℂ_def,smul_eq_mul]
  rw [show (2*z+r.natAbs)/2 = z+r.natAbs/2 by ring]
  push_cast
  ring

end GaussianMellin

section ArchimedeanFourier
open scoped FourierTransform ENNReal
private theorem realModelFourier (w : InfinitePlace F) (hw : w.IsReal) (g : ℝ → ℂ) (y : w.Completion) :
    F∞(w) (fun x ↦ g (realModel(hw) x)) y = 𝓕 g (realModel(hw) y) := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  let e := realModel(hw)
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  have hμ : infiniteLocalAdditiveTamagawaMeasure F w = (volume : Measure ℝ).map e.symm := dite_eq_left hw
  have hj : MeasurableEmbedding (e.symm : ℝ → w.Completion) := j.symm.toHomeomorph.measurableEmbedding
  rw [tamagawaFourier,hμ,hj.integral_map,Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with x
  have hχ : ψ∞(w) (e.symm x*y) = Real.fourierChar (inner ℝ x (e y)) := by
    rw [infiniteLocalCharacter_trace w e j.continuous,Real.fourierChar_apply',e.map_mul,e.apply_symm_apply]
    simp [mul_comm]
  change g (e (e.symm x)) * star (ψ∞(w) (e.symm x * y) : ℂ) = _
  rw [e.apply_symm_apply,hχ,Circle.star_addChar,Circle.smul_def,smul_eq_mul,mul_comm]

private theorem complexModelFourier (w : InfinitePlace F) (hw : w.IsComplex) (g : ℂ → ℂ) (y : w.Completion) :
    F∞(w) (fun x ↦ g (complexModel(hw) x)) y =
      2 * 𝓕 g ((2:ℝ) • star (complexModel(hw) y)) := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  let e := complexModel(hw)
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  have hμ : infiniteLocalAdditiveTamagawaMeasure F w = (2 • (volume : Measure ℂ)).map e.symm :=
    dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw)
  have hj : MeasurableEmbedding (e.symm : ℂ → w.Completion) := j.symm.toHomeomorph.measurableEmbedding
  rw [tamagawaFourier,hμ,hj.integral_map,show (2 • (volume : Measure ℂ)) = (2:ℝ≥0∞) • volume by simp [two_smul],
    integral_smul_measure,ENNReal.toReal_ofNat,Complex.real_smul,Complex.ofReal_ofNat,Real.fourier_eq]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  have hχ : ψ∞(w) (e.symm x*y) = Real.fourierChar (inner ℝ x ((2:ℝ) • star (e y))) := by
    rw [infiniteLocalCharacter_trace w e j.continuous,Real.fourierChar_apply',e.map_mul,e.apply_symm_apply,
      Algebra.trace_complex_apply,real_inner_smul_right]
    have hi : inner ℝ x (star (e y)) = (x*e y).re := by
      change (star (e y) * star x).re = _
      rw [← star_mul]
      exact Complex.conj_re _
    rw [hi]
  change g (e (e.symm x)) * star (ψ∞(w) (e.symm x * y) : ℂ) = _
  rw [e.apply_symm_apply,hχ,Circle.star_addChar,Circle.smul_def,smul_eq_mul,mul_comm]

private theorem euclideanGaussian_fourier {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (b : ℝ) (hb : 0<b) (y : E) :
    𝓕 (modelGaussian b : E → ℂ) y = ((Real.pi:ℂ)/b)^(Module.finrank ℝ E / 2:ℂ) *
      Complex.exp (-(Real.pi:ℂ)^2 * (‖y‖:ℂ)^2 / b) := by
  have hf : (modelGaussian b : E → ℂ) = fun x ↦ Complex.exp (-(b:ℂ)*(‖x‖:ℂ)^2) := by
    funext x
    simp [modelGaussian,Complex.ofReal_exp]
  rw [hf]
  exact fourier_gaussian_innerProductSpace (b := (b:ℂ)) hb y

private theorem realGaussian_fourier (a : Fin 2) :
    ∃ f : SchwartzMap ℝ ℂ, (∀ t : ℝ, f t = (t:ℂ)^a.val*modelGaussian Real.pi t) ∧
      ∀ t, 𝓕 f t = (-Complex.I)^a.val * f t := by
  obtain ⟨g,hg⟩ := exists_gaussian_schwartz (E := ℝ) Real.pi Real.pi_pos
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hF (t : ℝ) : 𝓕 g t = g t := by
    rw [SchwartzMap.fourier_coe,show (g:ℝ → ℂ) = modelGaussian Real.pi from funext hg,euclideanGaussian_fourier _ Real.pi_pos]
    rw [div_self hpi,Complex.one_cpow,one_mul,modelGaussian,Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp
  fin_cases a
  · exact ⟨g,fun t ↦ by simpa [modelGaussian] using hg t,fun t ↦ by simpa using hF t⟩
  · let f : SchwartzMap ℝ ℂ := (-2*(Real.pi:ℂ))⁻¹ • LineDeriv.lineDerivOp (1:ℝ) g
    have he (t : ℝ) : f t = (t:ℂ)*modelGaussian Real.pi t := by
      change _ * (LineDeriv.lineDerivOp (1:ℝ) g t) = _
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,show (g : ℝ → ℂ) = modelGaussian Real.pi from funext hg,
        modelGaussian_deriv]
      simp
      field_simp
    refine ⟨f,fun t ↦ by simpa using he t,fun t ↦ ?_⟩
    simp only [f,FourierTransform.fourier_smul,SchwartzMap.fourier_lineDerivOp_eq,smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply (Function.hasTemperateGrowth_inner_left (1:ℝ)),Complex.real_smul,
      smul_eq_mul,hF]
    change _ = (-Complex.I)^1 * f t
    rw [he,hg]
    simp [modelGaussian]
    field_simp

private theorem complexGaussian_fourier (r : ℤ) :
    ∃ f g : SchwartzMap ℂ ℂ,
      (∀ t, f t = (orientedCoord (decide (0≤r)) t)^r.natAbs * modelGaussian (2*Real.pi) t) ∧
      (∀ t, g t = (orientedCoord (decide (0≤ -r)) t)^(-r).natAbs * modelGaussian (2*Real.pi) t) ∧
      ∀ t, 2 * 𝓕 f ((2:ℝ) • star t) = (-Complex.I)^r.natAbs * g t := by
  obtain ⟨f,hf,hF⟩ := exists_harmonicGaussian (2*Real.pi) (by positivity) (decide (0≤r)) r.natAbs
  obtain ⟨g,hg,-⟩ := exists_harmonicGaussian (2*Real.pi) (by positivity) (decide (0≤ -r)) (-r).natAbs
  refine ⟨f,g,hf,hg,fun t ↦ ?_⟩
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hG : 𝓕 (modelGaussian (2*Real.pi) : ℂ → ℂ) ((2:ℝ) • star t) =
      (2:ℂ)⁻¹ * modelGaussian (2*Real.pi) t := by
    rw [euclideanGaussian_fourier _ (by positivity),Complex.finrank_real_complex,modelGaussian,Complex.ofReal_exp,norm_smul,norm_star]
    push_cast
    norm_num [Real.norm_of_nonneg,div_self hpi]
    congr 1
    · field_simp
    · congr 1
      field_simp
  have hp : (orientedCoord (decide (0≤r)) (star t))^r.natAbs =
      (orientedCoord (decide (0≤ -r)) t)^(-r).natAbs := by
    rcases lt_trichotomy r 0 with h|rfl|h
    · simp [orientedCoord,h.not_ge,h.le]
    · simp
    · simp [orientedCoord,h.le,h.not_ge]
  rw [hF,hG,hg,map_smul,Complex.real_smul,Complex.ofReal_ofNat,mul_pow,hp]
  push_cast
  rw [←mul_assoc ((-↑Real.pi*Complex.I/(2*↑Real.pi))^r.natAbs),←mul_pow]
  have hs : -((Real.pi:ℂ))*Complex.I/(2*Real.pi)*2 = -Complex.I := by field_simp
  rw [hs]
  ring

end ArchimedeanFourier

section ArchimedeanTateRatio
open scoped FourierTransform

private theorem realEuler_of_shape (w : InfinitePlace F) (hw : w.IsReal) (c : QuasiCharacter w.Completionˣ)
    (z : ℂ) (a : Fin 2) (h : realShape[hw,c,z,a]) :
    infiniteLocalEulerFactor w c = Complex.Gammaℝ (z+a.val) ∧ infiniteLocalEpsilonFactor w c = Complex.I^a.val := by
  have hp := (realLocalEulerParameters w hw c).unique (realLocalEulerParameters w hw c).exists.choose_spec (y₂ := (z,a)) h
  simp only [infiniteLocalEulerFactor,infiniteLocalEpsilonFactor,hw,↓reduceDIte,hp,and_self]

private theorem complexEuler_of_shape (w : InfinitePlace F) (hw : w.IsComplex) (c : QuasiCharacter w.Completionˣ)
    (z : ℂ) (r : ℤ) (h : complexShape[hw,c,z,r]) :
    infiniteLocalEulerFactor w c = Complex.Gammaℂ (z+r.natAbs/2)/2 ∧ infiniteLocalEpsilonFactor w c = Complex.I^r.natAbs := by
  have hp := (complexLocalEulerParameters w hw c).unique (complexLocalEulerParameters w hw c).exists.choose_spec (y₂ := (z,r)) h
  simp only [infiniteLocalEulerFactor,infiniteLocalEpsilonFactor,InfinitePlace.not_isReal_iff_isComplex.mpr hw,↓reduceDIte,hp,and_self]

private theorem exists_realModelTest (w : InfinitePlace F) (hw : w.IsReal) (g : SchwartzMap ℝ ℂ) :
    ∃ f : ℬ(w.Completion), test(f) = fun x ↦ g (realModel(hw) x) := by
  obtain ⟨E,hE⟩ := realSchwartzBruhat_equiv
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let e : Multiplicative w.Completion ≃ₜ* Multiplicative ℝ :=
    { (realModel(hw)).toAddEquiv.toMultiplicative with continuous_toFun := j.continuous,continuous_invFun := j.symm.continuous }
  exact ⟨⟨(E g).val ∘ e, schwartzBruhat_mem_comp_equiv e (E g).property⟩, funext fun x ↦ hE g (realModel(hw) x)⟩

private theorem tate_phase_cancel (n : ℕ) (A E D ρ : ℂ) (hA : A ≠ 0) (hD : D ≠ 0)
    (h : A*E = ρ*((-Complex.I)^n*(A*D))) : ρ = Complex.I^n*(E/D) := by
  have hi : Complex.I^n*(-Complex.I)^n=1 := by rw [←mul_pow];simp
  rw [←mul_div_assoc,eq_div_iff hD]
  apply mul_left_cancel₀ hA
  calc
    _ = Complex.I^n * (ρ*((-Complex.I)^n*(A*D))) := by
      conv_lhs => rw [←one_mul A,←hi]
      ring
    _ = _ := by rw [←h]; ring

private theorem zetaIntegral_const_mul {K : Type*} [NormedField K] [MeasurableSpace Kˣ]
    (μ : Measure Kˣ) (a : ℂ) (f : K → ℂ) (c : QuasiCharacter Kˣ) :
    localIdelicZetaIntegral μ (fun x ↦ a*f x) c = a*localIdelicZetaIntegral μ f c := by
  simp only [localIdelicZetaIntegral,mul_assoc,integral_const_mul]

private theorem realTate_ratio_strip (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) (s : ℂ) (hs : s.re ∈ Ioo (0:ℝ) 1) :
    let c := chart∞[w,χ] s
    infiniteLocalTateFactor w c = infiniteLocalEpsilonFactor w c *
      (infiniteLocalEulerFactor w c / infiniteLocalEulerFactor w (dualQuasiCharacter m∞(w) h∞(w) c)) := by
  obtain ⟨t,a,ht,hbase⟩ := realPlaceUnitary_shape w hw χ
  let c := chart∞[w,χ] s
  let d := dualQuasiCharacter m∞(w) h∞(w) c
  let z := s+t
  have hz : 0<z.re := by simpa [z,ht] using hs.1
  have hd : 0<(1-z).re := by simpa [z,ht] using sub_pos.mpr hs.2
  have h := realChart_shape w hw χ t a hbase s
  have h' := realDual_shape w hw c z a h
  obtain ⟨g,hg,hG⟩ := realGaussian_fourier a
  obtain ⟨f,hf⟩ := exists_realModelTest w hw g
  have hval (x : ℝ) : g x = (x:ℂ)^a.val * (Real.exp (-Real.pi*x^2):ℂ) := by simpa [modelGaussian,Real.norm_eq_abs,sq_abs] using hg x
  have hFT : F∞(w) test(f) = fun x ↦ (-Complex.I)^a.val * g (realModel(hw) x) := by
    rw [hf]
    exact funext fun y ↦ (realModelFourier w hw _ y).trans (hG _)
  have he := (infiniteLocalTateFactor_spec w).2 f χ s hs
  change localIdelicZetaIntegral μ∞(w) test(f) c = infiniteLocalTateFactor w c * localIdelicZetaIntegral μ∞(w) (F∞(w) test(f)) d at he
  rw [hFT,hf,realGaussian_integral w hw g c z a h hz hval,
    zetaIntegral_const_mul μ∞(w) _ (fun x ↦ g (realModel(hw) x)) d,
    realGaussian_integral w hw g d (1-z) a h' hd hval] at he
  have h₁ := realEuler_of_shape w hw c z a h
  have h₂ := realEuler_of_shape w hw d (1-z) a h'
  change infiniteLocalTateFactor w c = infiniteLocalEpsilonFactor w c * (infiniteLocalEulerFactor w c / infiniteLocalEulerFactor w d)
  rw [h₁.1,h₁.2,h₂.1]
  have hz' : 0 < (1-z+(a.val:ℂ)).re := by
    rw [Complex.add_re,Complex.natCast_re]
    positivity
  exact tate_phase_cancel _ 1 _ _ _ one_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz') (by simpa only [one_mul] using he)

private theorem complexTate_ratio_strip (w : InfinitePlace F) (hw : w.IsComplex)
    (χ : PontryaginDual w.Completionˣ) (s : ℂ) (hs : s.re ∈ Ioo (0:ℝ) 1) :
    let c := chart∞[w,χ] s
    infiniteLocalTateFactor w c = infiniteLocalEpsilonFactor w c *
      (infiniteLocalEulerFactor w c / infiniteLocalEulerFactor w (dualQuasiCharacter m∞(w) h∞(w) c)) := by
  obtain ⟨t,r,ht,hbase⟩ := complexPlaceUnitary_shape w hw χ
  let c := chart∞[w,χ] s
  let d := dualQuasiCharacter m∞(w) h∞(w) c
  let z := s+t
  have hz : 0<z.re := by simpa [z,ht] using hs.1
  have hd : 0<(1-z).re := by simpa [z,ht] using sub_pos.mpr hs.2
  have h := complexChart_shape w hw χ t r hbase s
  have h' := complexDual_shape w hw c z r h
  obtain ⟨g,g',hg,hg',hG⟩ := complexGaussian_fourier r
  let f : ℬ(w.Completion) := ⟨fun x ↦ g (complexModel(hw) x.toAdd), (complexModelSchwartz_iff w hw g).mpr ⟨g,rfl⟩⟩
  have hf : test(f) = fun x ↦ g (complexModel(hw) x) := rfl
  have hFT : F∞(w) test(f) = fun x ↦ (-Complex.I)^r.natAbs * g' (complexModel(hw) x) := by
    rw [hf]
    exact funext fun y ↦ (complexModelFourier w hw _ y).trans (hG _)
  have he := (infiniteLocalTateFactor_spec w).2 f χ s hs
  change localIdelicZetaIntegral μ∞(w) test(f) c = infiniteLocalTateFactor w c * localIdelicZetaIntegral μ∞(w) (F∞(w) test(f)) d at he
  rw [hFT,hf,complexGaussian_integral w hw g c z r h hz hg,
    zetaIntegral_const_mul μ∞(w) _ (fun x ↦ g' (complexModel(hw) x)) d,
    complexGaussian_integral w hw g' d (1-z) (-r) h' hd hg'] at he
  have h₁ := complexEuler_of_shape w hw c z r h
  have h₂ := complexEuler_of_shape w hw d (1-z) (-r) h'
  change infiniteLocalTateFactor w c = infiniteLocalEpsilonFactor w c * (infiniteLocalEulerFactor w c / infiniteLocalEulerFactor w d)
  rw [h₁.1,h₁.2,h₂.1,div_div_div_cancel_right₀ (by norm_num : (2:ℂ)≠0)]
  have hz' : 0 < (1-z+((-r).natAbs:ℂ)/2).re := by
    rw [Complex.add_re,Complex.div_ofNat_re,Complex.natCast_re]
    positivity
  apply tate_phase_cancel _ (Real.pi:ℂ) _ _ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) _ he
  rw [Complex.Gammaℂ_def]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (mul_pos zero_lt_two Real.pi_pos).ne'))))
    (Complex.Gamma_ne_zero_of_re_pos hz')

/-- Realize each sign parity as a unitary character in the real local field model. -/
private theorem realLocalTate_signCharacter (w : InfinitePlace F) (hw : w.IsReal) (a : Fin 2) :
    ∃ χ : PontryaginDual w.Completionˣ, ∀ x : ℝˣ,
      ((χ (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom x) :
        Circle) : ℂ) = (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ a.val := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hc : Continuous (fun x : ℝˣ ↦ (x : ℝ)) := Units.continuous_val
  have hpos : IsClopen {x : ℝˣ | 0 < (x : ℝ)} := by
    refine ⟨?_, isOpen_lt continuous_const hc⟩
    have he : {x : ℝˣ | 0 < (x : ℝ)} = {x : ℝˣ | 0 ≤ (x : ℝ)} :=
      Set.ext fun x ↦ by
        change 0 < (x : ℝ) ↔ 0 ≤ (x : ℝ)
        exact ⟨le_of_lt, fun hx ↦ lt_of_le_of_ne hx x.ne_zero.symm⟩
    rw [he]
    exact isClosed_le continuous_const hc
  let sign : ℝˣ →ₜ* Circle :=
    { toFun x := if 0 < (x : ℝ) then 1 else -1
      map_one' := by simp
      map_mul' x y := by
        change (if 0 < (x : ℝ) * (y : ℝ) then _ else _) = _
        rcases x.ne_zero.lt_or_gt with hx | hx <;> rcases y.ne_zero.lt_or_gt with hy | hy
        · simp [hx.not_gt, hy.not_gt, mul_pos_of_neg_of_neg hx hy]
        · simp [hx.not_gt, hy, (mul_neg_of_neg_of_pos hx hy).not_gt]
        · simp [hx, hy.not_gt, (mul_neg_of_pos_of_neg hx hy).not_gt]
        · simp [hx, hy, mul_pos hx hy]
      continuous_toFun := Continuous.if (by simp [hpos.frontier_eq]) continuous_const continuous_const }
  let i : w.Completionˣ →ₜ* ℝˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).continuous.units_map _⟩
  let power : Circle →ₜ* Circle := ⟨powMonoidHom a.val, continuous_pow a.val⟩
  refine ⟨power.comp (sign.comp i), fun x ↦ ?_⟩
  have he : i (Units.map e.symm.toMonoidHom x) = x := Units.ext (e.apply_symm_apply _)
  change ((sign (i (Units.map e.symm.toMonoidHom x)) ^ a.val : Circle) : ℂ) = _
  rw [he, Circle.coe_pow]
  change (↑(if 0 < (x : ℝ) then (1 : Circle) else -1) : ℂ) ^ a.val = _
  by_cases hx : 0 < (x : ℝ) <;> simp [hx]

/-- Tate's equation at a real place, in Euclidean coordinates on the strip of convergence.
The parity selects the sign character and its Fourier phase. -/
theorem realLocalTate_mellin_fourier (w : InfinitePlace F) (hw : w.IsReal)
    (f : SchwartzMap ℝ ℂ) (a : Fin 2) (z : ℂ) (hz : z.re ∈ Ioo (0 : ℝ) 1) :
    mellin (fun t : ℝ ↦ f t + (-1 : ℂ) ^ a.val * f (-t)) z =
      Complex.I ^ a.val * (Complex.Gammaℝ (z + a.val) / Complex.Gammaℝ (1 - z + a.val)) *
        mellin (fun t : ℝ ↦ (𝓕 f) t + (-1 : ℂ) ^ a.val * (𝓕 f) (-t)) (1 - z) := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  obtain ⟨χ, hχ⟩ := realLocalTate_signCharacter w hw a
  let c := chart∞[w,χ] z
  let d := dualQuasiCharacter m∞(w) h∞(w) c
  have hc := realChart_shape w hw χ 0 a (fun x ↦ by
    change (χ (Units.map e.symm.toMonoidHom x) : ℂ) = _
    simpa only [Complex.cpow_zero, one_mul] using hχ x) z
  simp only [add_zero] at hc
  have hd := realDual_shape w hw c z a hc
  have hdz : 0 < (1 - z).re := by simpa using sub_pos.mpr hz.2
  obtain ⟨g, hg⟩ := exists_realModelTest w hw f
  have hft : F∞(w) (fun x ↦ f (e x)) = fun y ↦ (𝓕 f) (e y) :=
    funext (realModelFourier w hw (f : ℝ → ℂ))
  have h := (infiniteLocalTateFactor_spec w).2 g χ z hz
  change localIdelicZetaIntegral μ∞(w) (fun x ↦ g (Multiplicative.ofAdd x)) c =
    infiniteLocalTateFactor w c * localIdelicZetaIntegral μ∞(w) (F∞(w) _) d at h
  rw [hg, hft, realIntegral_shape w hw f c z a hc hz.1,
    realIntegral_shape w hw (𝓕 f) d (1 - z) a hd hdz] at h
  have hratio := realTate_ratio_strip w hw χ z hz
  change infiniteLocalTateFactor w c = infiniteLocalEpsilonFactor w c *
    (infiniteLocalEulerFactor w c / infiniteLocalEulerFactor w d) at hratio
  have h₁ := realEuler_of_shape w hw c z a hc
  have h₂ := realEuler_of_shape w hw d (1 - z) a hd
  rw [h₁.1, h₁.2, h₂.1] at hratio
  rwa [hratio] at h

/-- Realize an integral angular weight by a unitary character on a complex completion. -/
private theorem complexLocalTate_angularCharacter (w : InfinitePlace F) (hw : w.IsComplex) (k : ℤ) :
    ∃ χ : PontryaginDual w.Completionˣ, ∀ x : ℂˣ,
      ((χ (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom x) :
        Circle) : ℂ) = ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ k := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let phase : ℂˣ →ₜ* Circle :=
    { toFun x := ⟨(x : ℂ) / (‖(x : ℂ)‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
        rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr x.ne_zero)])⟩
      map_one' := by ext; simp
      map_mul' x y := by
        apply Subtype.ext
        change ((x : ℂ) * (y : ℂ)) / (‖(x : ℂ) * (y : ℂ)‖ : ℂ) = _
        rw [norm_mul, Complex.ofReal_mul, mul_div_mul_comm]
        rfl
      continuous_toFun := (Units.continuous_val.div
        (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val))
        (fun x ↦ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))).subtype_mk _ }
  let i : w.Completionˣ →ₜ* ℂˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).continuous.units_map _⟩
  let power : Circle →ₜ* Circle := ⟨zpowGroupHom k, continuous_zpow k⟩
  refine ⟨power.comp (phase.comp i), fun x ↦ ?_⟩
  have he : i (Units.map e.symm.toMonoidHom x) = x := Units.ext (e.apply_symm_apply _)
  change ((phase (i (Units.map e.symm.toMonoidHom x)) ^ k : Circle) : ℂ) = _
  rw [he, Circle.coe_zpow]
  rfl

/-- Tate's equation at a complex place in polar coordinates on the strip of convergence.
The Fourier transform uses the trace pairing and reverses the angular exponent. -/
theorem complexLocalTate_mellin_fourier (w : InfinitePlace F) (hw : w.IsComplex)
    (f fHat : SchwartzMap ℂ ℂ) (hfHat : ∀ x : ℂ, fHat x = 2 * (𝓕 f) (2 * star x))
    (k : ℤ) (z : ℂ) (hz : z.re ∈ Ioo (0 : ℝ) 1) :
    let M (g : SchwartzMap ℂ ℂ) (j : ℤ) (s : ℂ) := 2 * mellin
      (fun t : ℝ ↦ ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I) *
        g ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (2 * s)
    M f k z = Complex.I ^ k.natAbs *
      (Complex.Gammaℂ (z + (k.natAbs : ℂ) / 2) / Complex.Gammaℂ (1 - z + (k.natAbs : ℂ) / 2)) *
      M fHat (-k) (1 - z) := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  obtain ⟨χ, hχ⟩ := complexLocalTate_angularCharacter w hw k
  let c := chart∞[w,χ] z
  let d := dualQuasiCharacter m∞(w) h∞(w) c
  have hc := complexChart_shape w hw χ 0 k (fun x ↦ by
    change (χ (Units.map e.symm.toMonoidHom x) : ℂ) = _
    simpa only [Complex.cpow_zero, one_mul] using hχ x) z
  simp only [add_zero] at hc
  have hd := complexDual_shape w hw c z k hc
  have hdz : 0 < (1 - z).re := by simpa using sub_pos.mpr hz.2
  let g : SchwartzBruhat (Multiplicative w.Completion) := ⟨fun x ↦ f (e x.toAdd),
    (complexModelSchwartz_iff w hw f).mpr ⟨f, rfl⟩⟩
  have hft : F∞(w) (fun x ↦ f (e x)) = fun y ↦ fHat (e y) := by
    funext y
    rw [hfHat, SchwartzMap.fourier_coe]
    simpa only [Complex.real_smul, Complex.ofReal_ofNat] using complexModelFourier w hw (f : ℂ → ℂ) y
  have h := (infiniteLocalTateFactor_spec w).2 g χ z hz
  change localIdelicZetaIntegral μ∞(w) (fun x ↦ f (e x)) c =
    infiniteLocalTateFactor w c * localIdelicZetaIntegral μ∞(w) (F∞(w) (fun x ↦ f (e x))) d at h
  rw [hft, complexIntegral_shape w hw f c z k hc hz.1,
    complexIntegral_shape w hw fHat d (1 - z) (-k) hd hdz] at h
  have hratio := complexTate_ratio_strip w hw χ z hz
  change infiniteLocalTateFactor w c = infiniteLocalEpsilonFactor w c *
    (infiniteLocalEulerFactor w c / infiniteLocalEulerFactor w d) at hratio
  have h₁ := complexEuler_of_shape w hw c z k hc
  have h₂ := complexEuler_of_shape w hw d (1 - z) (-k) hd
  rw [h₁.1, h₁.2, h₂.1, div_div_div_cancel_right₀ (by norm_num : (2 : ℂ) ≠ 0), Int.natAbs_neg] at hratio
  have hp (g : SchwartzMap ℂ ℂ) (j : ℤ) : angularProfile g j =
      fun t : ℝ ↦ ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I) *
        g ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    funext t
    simp only [angularProfile, angularWeight, Int.cast_one, one_mul]
  simpa only [hratio, hp] using h

end ArchimedeanTateRatio

private theorem finiteEuler_chart_meromorphic (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    let E (s : ℂ) := finiteLocalEulerFactor v (chart𝔭[v,χ] s)
    Meromorphic E ∧ ∀ s, 0 < s.re → E s ≠ 0 := by
  classical
  let c := (circleToComplex).comp χ
  let hπ := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.adicCompletion F)ˣ := Units.mk0 (hπ.choose : v.adicCompletion F) hπ.choose_spec.ne_zero
  let b := ‖π.val‖
  have hb : 0<b := norm_pos_iff.mpr π.ne_zero
  have hb' : b < 1 := by
    change ‖(hπ.choose : v.adicCompletion F)‖ < 1
    rw [norm_uniformizer_adicCompletion v _ hπ.choose_spec]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hu (z : ℂ) (u : (v.adicCompletionIntegers F)ˣ) :
      let y := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
      chart𝔭[v,χ] z y = c y := by
    change c _ * (‖_‖:ℂ)^z = _
    rw [finite_integer_unit_norm v u,Complex.ofReal_one,Complex.one_cpow,mul_one]
  have he (z : ℂ) : finiteLocalEulerFactor v (chart𝔭[v,χ] z) =
      if unramified[v,c] then (1 - (χ π:ℂ)*(b:ℂ)^z)⁻¹ else 1 := by
    have h : unramified[v,chart𝔭[v,χ] z] ↔ unramified[v,c] :=
      ⟨fun h u ↦ (hu z u).symm.trans (h u),fun h u ↦ (hu z u).trans (h u)⟩
    simp only [finiteLocalEulerFactor,h]
    rfl
  by_cases h : unramified[v,c]
  · have hE : (fun z ↦ finiteLocalEulerFactor v (chart𝔭[v,χ] z)) =
        fun z : ℂ ↦ (1 - (χ π:ℂ)*(b:ℂ)^z)⁻¹ := funext fun z ↦ (he z).trans (ite_eq_left h)
    dsimp only
    rw [hE]
    have hA : Differentiable ℂ (fun z : ℂ ↦ 1 - (χ π:ℂ)*(b:ℂ)^z) :=
      (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne')) |>.const_mul _).const_sub _
    refine ⟨fun z ↦ (hA.analyticAt z).meromorphicAt.inv,fun z hz ↦ (congrFun hE z).trans_ne (inv_ne_zero (sub_ne_zero.mpr ?_))⟩
    intro ez
    have hn := congrArg norm ez
    rw [norm_one,norm_mul,Circle.norm_coe,one_mul,Complex.norm_cpow_eq_rpow_re_of_pos hb] at hn
    exact (Real.rpow_lt_one hb.le hb' hz).ne hn.symm
  · have hE : (fun z ↦ finiteLocalEulerFactor v (chart𝔭[v,χ] z)) = fun _ : ℂ ↦ 1 :=
      funext fun z ↦ (he z).trans (ite_eq_right h)
    dsimp only
    rw [hE]
    exact ⟨fun _ ↦ MeromorphicAt.const _ _,fun z _ ↦ (congrFun hE z).trans_ne one_ne_zero⟩

private theorem finiteTate_ratio_germ (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    ∀ᶠ z : ℂ in 𝓝[≠] (1/2:ℂ), let c := chart𝔭[v,χ] z
      finiteLocalTateFactor v c = finiteLocalEpsilonFactor v c *
        (finiteLocalEulerFactor v c / finiteLocalEulerFactor v (dualQuasiCharacter m𝔭(v) h𝔭(v) c)) := by
  let E (η : PontryaginDual (v.adicCompletion F)ˣ) (z : ℂ) := finiteLocalEulerFactor v (chart𝔭[v,η] z)
  let ρ (z : ℂ) := finiteLocalTateFactor v (chart𝔭[v,χ] z)
  let H (z : ℂ) := ρ z / E χ z * E χ⁻¹ (1-z)
  have hm : Meromorphic H := fun z ↦ (((finiteLocalTateFactor_spec v).1 χ).meromorphicOn z trivial
    |>.div ((finiteEuler_chart_meromorphic v χ).1 z)).mul
    (((finiteEuler_chart_meromorphic v χ⁻¹).1 (1-z)).comp_analyticAt (g := fun t : ℂ ↦ 1-t) (by fun_prop))
  have he (z : ℂ) : finiteLocalEpsilonFactor v (chart𝔭[v,χ] z) = toMeromorphicNFOn H univ z := by
    unfold finiteLocalEpsilonFactor
    simp only [norm_chart_twist,dual_norm_chart]
    change toMeromorphicNFOn (fun t : ℂ ↦ H (z+t)) univ 0 = _
    have hH : MeromorphicOn (fun t : ℂ ↦ H (z+t)) univ := fun t _ ↦ (hm (z+t)).comp_analyticAt (g := fun u : ℂ ↦ z+u) (by fun_prop)
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hH (mem_univ 0)]
    exact normalize_translate_at_zero (fun t _ ↦ hm t) z
  have hnear := (show MeromorphicOn H univ from fun z _ ↦ hm z).toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ (1/2:ℂ))
  have hstrip : ∀ᶠ z in 𝓝[≠] (1/2:ℂ), z.re ∈ Ioo (0:ℝ) 1 :=
    nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds (by norm_num [mem_preimage,mem_Ioo]))
  filter_upwards [hnear,hstrip] with z h hz
  dsimp only
  rw [he,h,dual_norm_chart]
  change ρ z = (ρ z / E χ z * E χ⁻¹ (1-z)) * (E χ z / E χ⁻¹ (1-z))
  have h₁ := (finiteEuler_chart_meromorphic v χ).2 z hz.1
  have h₂ := (finiteEuler_chart_meromorphic v χ⁻¹).2 (1-z) (by simpa using sub_pos.mpr hz.2)
  field_simp [show E χ z ≠ 0 from h₁, show E χ⁻¹ (1-z) ≠ 0 from h₂]

/-- Paper: Equation (3.3.1.32), p. 136. As meromorphic functions, the
correcting factor is epsilon times the Euler factor divided by its dual.
Deviation: The equality is expressed off a discrete set of exponents. -/
theorem sLocalRhoFactor_eq_epsilon_mul (χ : PontryaginDual Jₛ) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      let c := chartₛ(χ) s
      sLocalRhoFactor c = sLocalEpsilonFactor c *
        (sLocalHeckeL c / sLocalHeckeL (dualQuasiCharacter (G := Jₛ) mₛ hmₛ c)) := by
  classical
  let E (z : ℂ) := sLocalEpsilonFactor (chartₛ(χ) z)
  let L (η : PontryaginDual Jₛ) (z : ℂ) := sLocalHeckeL (chartₛ(η) z)
  have hm (η : PontryaginDual Jₛ) : Meromorphic (L η) := by
    intro z
    have h : MeromorphicAt (L η)⁻¹ z := ((differentiable_inv_sLocalHeckeL η).analyticAt z).meromorphicAt
    simpa only [inv_inv] using h.inv
  have hE : Differentiable ℂ E := fun z ↦ ((sLocalEpsilonFactor_entire χ) z trivial).differentiableAt
  have hmid : ∀ᶠ z : ℂ in 𝓝[≠] (1/2:ℂ), z.re ∈ Ioo (0:ℝ) 1 :=
    nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds (by norm_num [mem_preimage,mem_Ioo]))
  let c := chartₛ(χ)
  let d (z : ℂ) := dualQuasiCharacter (G := Jₛ) mₛ hmₛ (c z)
  have hinf (w : InfinitePlace F) : ∀ᶠ z in 𝓝[≠] (1/2:ℂ),
      let a := sLocalInfiniteRestriction w (c z)
      infiniteLocalTateFactor w a = infiniteLocalEpsilonFactor w a *
        (infiniteLocalEulerFactor w a / infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (d z))) := by
    obtain ⟨η,ha,hd⟩ := sLocalInfinite_charts χ w
    filter_upwards [hmid] with z hz
    dsimp only
    rw [ha z,hd z]
    by_cases hw : w.IsReal
    · exact realTate_ratio_strip w hw η z hz
    · exact complexTate_ratio_strip w (InfinitePlace.not_isReal_iff_isComplex.mp hw) η z hz
  have hfin (v : S) : ∀ᶠ z in 𝓝[≠] (1/2:ℂ),
      let a := sLocalFiniteRestriction v (c z)
      finiteLocalTateFactor v.val a = finiteLocalEpsilonFactor v.val a *
        (finiteLocalEulerFactor v.val a / finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (d z))) := by
    obtain ⟨η,ha,hd⟩ := sLocalFinite_charts χ v
    filter_upwards [finiteTate_ratio_germ v.val η] with z hz
    dsimp only
    rw [ha z,hd z]
    exact hz
  have hratio : (fun z ↦ sLocalRhoFactor (c z)) =ᶠ[codiscrete ℂ] fun z ↦ E z * (L χ z / L χ⁻¹ (1-z)) := by
    apply meromorphic_eq_of_germ (sLocalRhoFactor_meromorphic χ)
      (fun z ↦ (hE.analyticAt z).meromorphicAt.mul ((hm χ z).div ((hm χ⁻¹ (1-z)).comp_analyticAt
        (g := fun t : ℂ ↦ 1-t) (by fun_prop)))) (z := 1/2)
    filter_upwards [eventually_all.mpr hinf,eventually_all.mpr hfin] with z h₁ h₂
    change sLocalRhoFactor (c z) = sLocalEpsilonFactor (c z) *
      (sLocalHeckeL (c z) / sLocalHeckeL (chartₛ(χ⁻¹) (1-z)))
    rw [← sLocal_dual_chart]
    change sLocalRhoFactor (c z) = sLocalEpsilonFactor (c z) * (sLocalHeckeL (c z)/sLocalHeckeL (d z))
    simp only [sLocalRhoFactor,sLocalEpsilonFactor,sLocalHeckeL,h₁,h₂,Finset.prod_mul_distrib,div_eq_mul_inv,mul_inv,Finset.prod_inv_distrib]
    ring
  filter_upwards [hratio] with z hz
  change sLocalRhoFactor (c z) = E z * (L χ z / sLocalHeckeL (d z))
  rw [show d z = chartₛ(χ⁻¹) (1-z) from sLocal_dual_chart χ z]
  exact hz

/-- Every S-local quasi-character belongs to the unitary chart obtained by
removing the real power given by its abscissa. -/
private theorem exists_sLocal_chart (c : QuasiCharacter Jₛ) :
    ∃ (χ : PontryaginDual Jₛ) (s : ℂ), c = chartₛ(χ) s := by
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  have hne : ∃ g, mₛ g ≠ 1 := by
    obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨τ t, (hτ t).trans_ne ht⟩
  exact exists_unitary_norm_chart mₛ hmₛ (isProperMap_sIdeleQuotientNorm F S) hne c

/-- Paper: Lemma 3.3.1.7(3)(b), p. 136. The S-local epsilon factor is nowhere zero. -/
theorem sLocalEpsilonFactor_ne_zero (c : QuasiCharacter Jₛ) :
    sLocalEpsilonFactor c ≠ 0 := by
  obtain ⟨χ, s, rfl⟩ := exists_sLocal_chart c
  let x : Jₛ := QuotientGroup.mk (-1 : (SAdeleRing F S)ˣ)
  let E (z : ℂ) := sLocalEpsilonFactor (chartₛ(χ) z)
  let E' (z : ℂ) := sLocalEpsilonFactor (chartₛ(χ⁻¹) (1 - z))
  have href : Tendsto (fun z : ℂ ↦ 1 - z) (𝓝[≠] s) (𝓝[≠] (1 - s)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_const.sub continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact fun he ↦ hz (sub_right_inj.mp he)
  have heq : E * E' =ᶠ[𝓝[≠] s] fun z ↦ chartₛ(χ) z x := by
    filter_upwards [nhdsNE_le_codiscrete s (sLocalRhoFactor_mul_dual χ),
      nhdsNE_le_codiscrete s (sLocalRhoFactor_eq_epsilon_mul χ),
      href.eventually (nhdsNE_le_codiscrete (1 - s) (sLocalRhoFactor_eq_epsilon_mul χ⁻¹))]
      with z hr h₁ h₂
    let d := chartₛ(χ) z
    let d' := chartₛ(χ⁻¹) (1 - z)
    have hd : dualQuasiCharacter mₛ hmₛ d = d' := sLocal_dual_chart χ z
    have hd' : dualQuasiCharacter mₛ hmₛ d' = d :=
      (congrArg (dualQuasiCharacter mₛ hmₛ) hd.symm).trans (dualQuasiCharacter_involutive _ _ d)
    let a := sLocalHeckeL (chartₛ(χ) z)
    let b := sLocalHeckeL (chartₛ(χ⁻¹) (1 - z))
    change sLocalRhoFactor d = E z * (a / sLocalHeckeL (dualQuasiCharacter mₛ hmₛ d)) at h₁
    change sLocalRhoFactor d' = E' z * (b / sLocalHeckeL (dualQuasiCharacter mₛ hmₛ d')) at h₂
    rw [hd] at h₁
    rw [hd'] at h₂
    change sLocalRhoFactor d * sLocalRhoFactor (dualQuasiCharacter mₛ hmₛ d) = d x at hr
    rw [hd] at hr
    have hprod : (E z * (a / b)) * (E' z * (b / a)) = d x :=
      (congrArg₂ (· * ·) h₁ h₂).symm.trans hr
    have hne : chartₛ(χ) z x ≠ 0 := ((Group.isUnit x).map _).ne_zero
    have ha : a ≠ 0 := fun h ↦ hne (by simpa [h] using hprod.symm)
    have hb : b ≠ 0 := fun h ↦ hne (by simpa [h] using hprod.symm)
    refine Eq.trans ?_ hprod
    change E z * E' z = (E z * (a / b)) * (E' z * (b / a))
    field_simp
  have h₁ : ContinuousAt E s := ((sLocalEpsilonFactor_entire χ) s trivial).continuousAt
  have h₂ : ContinuousAt E' s := ((sLocalEpsilonFactor_entire χ⁻¹) (1 - s) trivial).continuousAt.comp
    (continuous_const.sub continuous_id).continuousAt
  have h₃ : ContinuousAt (fun z ↦ chartₛ(χ) z x) s := by
    let N : ℂ := (((mₛ x : ℝ≥0) : ℝ) : ℂ)
    have hn : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ x).ne_zero)
    exact continuousAt_const.mul (differentiableAt_id.const_cpow (Or.inl hn)).continuousAt
  have h := tendsto_nhds_unique_of_eventuallyEq
    ((h₁.mul h₂).tendsto.mono_left nhdsWithin_le_nhds) (h₃.tendsto.mono_left nhdsWithin_le_nhds) heq
  exact left_ne_zero_of_mul ((h.trans_ne ((Group.isUnit x).map _).ne_zero))

/-- A nonnegative real base commutes with conjugating the exponent. -/
private theorem star_ofReal_cpow_of_nonneg {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    star ((r : ℂ) ^ z) = (r : ℂ) ^ (star z) := by
  have h := Complex.cpow_conj (r : ℂ) z (by rw [Complex.arg_ofReal_of_nonneg hr]; exact Real.pi_ne_zero.symm)
  rw [Complex.conj_ofReal] at h
  exact h.symm

/-- The archimedean Euler factor of the pointwise conjugate quasi-character
is the conjugate Euler factor. -/
private theorem infiniteLocalEulerFactor_conj (w : InfinitePlace F)
    (c d : QuasiCharacter w.Completionˣ) (h : ∀ g, d g = star (c g)) :
    infiniteLocalEulerFactor w d = star (infiniteLocalEulerFactor w c) := by
  by_cases hw : w.IsReal
  · have hp := (realLocalEulerParameters w hw c).exists.choose_spec
    have hshape : realShape[hw, d, star (realLocalEulerParameters w hw c).exists.choose.1,
        (realLocalEulerParameters w hw c).exists.choose.2] := by
      intro x
      rw [h, hp x, star_mul', star_pow, star_ofReal_cpow_of_nonneg (norm_nonneg _)]
      congr 2
      split_ifs <;> simp
    have hu := (realLocalEulerParameters w hw d).unique
      (realLocalEulerParameters w hw d).exists.choose_spec
      (y₂ := (star (realLocalEulerParameters w hw c).exists.choose.1,
        (realLocalEulerParameters w hw c).exists.choose.2)) hshape
    simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hu]
    rw [Complex.star_def, ← Complex.Gammaℝ_conj, map_add, Complex.conj_natCast, ← Complex.star_def]
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    have hp := (complexLocalEulerParameters w hc c).exists.choose_spec
    have hshape : complexShape[hc, d, star (complexLocalEulerParameters w hc c).exists.choose.1,
        -(complexLocalEulerParameters w hc c).exists.choose.2] := by
      intro x
      have hx : (‖(x : ℂ)‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)
      have hn : ‖(x : ℂ) / (‖(x : ℂ)‖ : ℂ)‖ = 1 := by
        rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr x.ne_zero)]
      rw [h, hp x, star_mul', star_ofReal_cpow_of_nonneg (by positivity), zpow_neg, ← inv_zpow,
        Complex.inv_eq_conj hn, ← Complex.star_def, star_zpow₀]
    have hu := (complexLocalEulerParameters w hc d).unique
      (complexLocalEulerParameters w hc d).exists.choose_spec
      (y₂ := (star (complexLocalEulerParameters w hc c).exists.choose.1,
        -(complexLocalEulerParameters w hc c).exists.choose.2)) hshape
    simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hu, Int.natAbs_neg]
    rw [Complex.star_def, map_div₀, ← Complex.Gammaℂ_conj, map_add, map_div₀, Complex.conj_natCast,
      map_ofNat]

/-- The finite Euler factor of the pointwise conjugate quasi-character is the
conjugate Euler factor. -/
private theorem finiteLocalEulerFactor_conj (v : Primes)
    (c d : QuasiCharacter (v.adicCompletion F)ˣ) (h : ∀ g, d g = star (c g)) :
    finiteLocalEulerFactor v d = star (finiteLocalEulerFactor v c) := by
  have hiff : unramified[v, d] ↔ unramified[v, c] := by
    refine forall_congr' fun u ↦ ?_
    rw [h]
    exact ⟨fun e ↦ by simpa using congrArg star e, fun e ↦ by rw [e, star_one]⟩
  unfold finiteLocalEulerFactor
  by_cases hc : unramified[v, c]
  · rw [if_pos hc, if_pos (hiff.mpr hc)]
    dsimp only
    rw [h, star_inv₀, star_sub, star_one]
  · rw [if_neg hc, if_neg (fun e ↦ hc (hiff.mp e)), star_one]

/-- The partial Euler product of the pointwise conjugate quasi-character is
the conjugate partial Euler product. -/
private theorem sLocalHeckeL_conj (c d : QuasiCharacter Jₛ) (h : ∀ g, d g = star (c g)) :
    sLocalHeckeL d = star (sLocalHeckeL c) := by
  unfold sLocalHeckeL
  rw [Complex.star_def, map_mul, map_prod, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [← Complex.star_def]
    exact infiniteLocalEulerFactor_conj w _ _ fun g ↦ h _
  · refine Finset.prod_congr rfl fun v _ ↦ ?_
    rw [← Complex.star_def]
    exact finiteLocalEulerFactor_conj v.val _ _ fun g ↦ h _

/-- Paper: Lemma 3.3.1.7(3)(b), p. 136. The S-local epsilon factor has
modulus one on the critical line. -/
theorem sLocalEpsilonFactor_norm_criticalLine (χ : PontryaginDual Jₛ) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖sLocalEpsilonFactor (chartₛ(χ) s)‖ = 1 := by
  let E (z : ℂ) := sLocalEpsilonFactor (chartₛ(χ) z)
  have hE : Continuous E :=
    continuousOn_univ.mp (sLocalEpsilonFactor_entire χ).continuousOn
  let γ (t : ℝ) : ℂ := s + (t : ℂ) * Complex.I
  have hγc : Continuous γ := by fun_prop
  have hγ0 : γ 0 = s := by simp [γ]
  have hγ : Tendsto γ (𝓝[≠] 0) (𝓝[≠] s) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact hγ0 ▸ (hγc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      intro he
      apply ht
      have h1 : (t : ℂ) * Complex.I = 0 := by
        have := congrArg (· - s) he
        simpa [γ] using this
      simpa using h1
  have hkey (z : ℂ) (hz : z.re = 1 / 2)
      (hρ : sLocalRhoFactor (chartₛ(χ) z) = sLocalEpsilonFactor (chartₛ(χ) z) *
        (sLocalHeckeL (chartₛ(χ) z) /
          sLocalHeckeL (dualQuasiCharacter (G := Jₛ) mₛ hmₛ (chartₛ(χ) z)))) :
      ‖E z‖ = 1 := by
    have hn := sLocalRhoFactor_norm_criticalLine χ z hz
    have hreflect : 1 - z = star z := by
      apply Complex.ext <;> norm_num [Complex.sub_re, hz]
    have hd : dualQuasiCharacter (G := Jₛ) mₛ hmₛ (chartₛ(χ) z) = chartₛ(χ⁻¹) (star z) := by
      rw [sLocal_dual_chart, hreflect]
    have hL : sLocalHeckeL (chartₛ(χ⁻¹) (star z)) = star (sLocalHeckeL (chartₛ(χ) z)) :=
      sLocalHeckeL_conj _ _ (sLocal_chart_conj χ z)
    rw [hd, hL] at hρ
    have hL0 : sLocalHeckeL (chartₛ(χ) z) ≠ 0 := by
      intro h0
      rw [h0, zero_div, mul_zero] at hρ
      rw [hρ, norm_zero] at hn
      exact zero_ne_one hn
    rw [hρ, norm_mul, norm_div, norm_star, div_self (norm_ne_zero_iff.mpr hL0), mul_one] at hn
    exact hn
  have hev : (fun t : ℝ ↦ ‖E (γ t)‖) =ᶠ[𝓝[≠] 0] fun _ ↦ (1 : ℝ) := by
    filter_upwards [hγ.eventually (nhdsNE_le_codiscrete s (sLocalRhoFactor_eq_epsilon_mul χ))]
      with t ht
    exact hkey (γ t) (by simp [γ, hs]) ht
  have hlim := tendsto_nhds_unique_of_eventuallyEq
    (((hE.comp hγc).norm.tendsto 0).mono_left nhdsWithin_le_nhds) tendsto_const_nhds hev
  change ‖E (γ 0)‖ = 1 at hlim
  rwa [hγ0] at hlim

/-- If a function on the plane is meromorphic with no poles, then normalizing each
of its translates and evaluating at the origin gives an entire function. -/
private theorem analyticOnNhd_toMeromorphicNFOn_translate {H : ℂ → ℂ}
    (hH : MeromorphicOn H univ) (hord : ∀ s, 0 ≤ meromorphicOrderAt H s) :
    AnalyticOnNhd ℂ (fun s ↦ toMeromorphicNFOn (fun t ↦ H (s + t)) univ 0) univ := by
  let G := toMeromorphicNFOn H univ
  have hG (s : ℂ) : AnalyticAt ℂ G s :=
    (meromorphicNFOn_toMeromorphicNFOn H univ (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (by rw [meromorphicOrderAt_toMeromorphicNFOn hH (mem_univ s)]; exact hord s)
  have heq (s : ℂ) : toMeromorphicNFOn (fun t ↦ H (s + t)) univ 0 = G s := by
    have hm : MeromorphicOn (fun t ↦ H (s + t)) univ := fun t _ ↦ by
      have := (hH (s + t) (mem_univ _)).comp_analyticAt (g := fun t ↦ s + t) (by fun_prop)
      exact this
    have hGs : AnalyticAt ℂ (fun t ↦ G (s + t)) 0 :=
      (by simpa using hG s : AnalyticAt ℂ G (s + 0)).comp (by fun_prop)
    have hnear : (fun t ↦ H (s + t)) =ᶠ[𝓝[≠] 0] fun t ↦ G (s + t) := by
      have ht : Tendsto (fun t : ℂ ↦ s + t) (𝓝[≠] 0) (𝓝[≠] s) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · exact (by simpa using (continuous_const_add s).tendsto (0 : ℂ) :
            Tendsto (fun t : ℂ ↦ s + t) (𝓝 0) (𝓝 s)).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          simpa using ht
      exact ht.eventually (hH.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)).symm
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ 0),
      (toMeromorphicNFAt_eventuallyEq_nhds_congr hnear).eq_of_nhds,
      toMeromorphicNFAt_eq_self.mpr hGs.meromorphicNFAt]
    simp only [add_zero]
  intro s _
  rw [show (fun s ↦ toMeromorphicNFOn (fun t ↦ H (s + t)) univ 0) = G from funext heq]
  exact hG s

/-- Paper: Lemma 3.3.1.7(2), p. 135. Dividing by the Euler product removes
all poles of the S-local zeta function. -/
theorem sLocalNormalizedZFunction_entire (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalNormalizedZFunction f (chartₛ(χ) s)) univ := by
  -- Z / L = Z · L⁻¹ with L⁻¹ entire; a pole of Z is a pole of ρ = ε · L / L̂,
  -- whose order is at most the order of the zero of L⁻¹.
  let Z : ℂ → ℂ := fun u ↦ sLocalIdelicZFunction f (chartₛ(χ) u)
  let Λ : ℂ → ℂ := fun u ↦ (sLocalHeckeL (chartₛ(χ) u))⁻¹
  let Λ' : ℂ → ℂ := fun u ↦ (sLocalHeckeL (chartₛ(χ⁻¹) (1 - u)))⁻¹
  let ε : ℂ → ℂ := fun u ↦ sLocalEpsilonFactor (chartₛ(χ) u)
  have hΛ : Differentiable ℂ Λ := differentiable_inv_sLocalHeckeL χ
  have hΛ' : Differentiable ℂ Λ' :=
    (differentiable_inv_sLocalHeckeL χ⁻¹).comp (by fun_prop)
  have hZ : MeromorphicOn Z univ := (sLocalIdelicZFunction_meromorphic f χ).meromorphicOn
  have hH : MeromorphicOn (Z * Λ) univ := fun s _ ↦
    (hZ s (mem_univ s)).mul (hΛ.analyticAt s).meromorphicAt
  have hord (s : ℂ) : 0 ≤ meromorphicOrderAt (Z * Λ) s := by
    have hΛo := (hΛ.analyticAt s).meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_mul (hZ s (mem_univ s)) (hΛ.analyticAt s).meromorphicAt]
    rcases le_or_gt 0 (meromorphicOrderAt Z s) with hz | hz
    · exact add_nonneg hz hΛo
    have hρ := (min_le_iff.mp (sLocalIdelicZFunction_poles f χ s)).resolve_left (not_le.mpr hz)
    have hρeq : (fun z ↦ sLocalRhoFactor (chartₛ(χ) z)) =ᶠ[𝓝[≠] s] ε * (Λ⁻¹ * Λ') := by
      filter_upwards [nhdsNE_le_codiscrete s (sLocalRhoFactor_eq_epsilon_mul χ)] with u hu
      simp only at hu
      simp only [Pi.mul_apply, Pi.inv_apply, ε, Λ, Λ', inv_inv, hu, div_eq_mul_inv,
        sLocal_dual_chart]
    have hε := ((sLocalEpsilonFactor_entire χ) s (mem_univ s))
    rw [meromorphicOrderAt_congr hρeq, meromorphicOrderAt_mul hε.meromorphicAt
      ((hΛ.analyticAt s).meromorphicAt.inv.mul (hΛ'.analyticAt s).meromorphicAt),
      meromorphicOrderAt_mul (hΛ.analyticAt s).meromorphicAt.inv (hΛ'.analyticAt s).meromorphicAt,
      meromorphicOrderAt_inv] at hρ
    have hεo := hε.meromorphicOrderAt_nonneg
    have hΛ'o := (hΛ'.analyticAt s).meromorphicOrderAt_nonneg
    generalize meromorphicOrderAt Z s = a at *
    generalize meromorphicOrderAt Λ s = l at *
    generalize meromorphicOrderAt ε s = e at *
    generalize meromorphicOrderAt Λ' s = l' at *
    induction l using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      induction a using WithTop.recTopCoe with
      | top => exact absurd hz (not_lt.mpr le_top)
      | coe a =>
        induction e using WithTop.recTopCoe with
        | top => simp at hρ
        | coe e =>
          induction l' using WithTop.recTopCoe with
          | top => simp at hρ
          | coe l' =>
            rw [← WithTop.LinearOrderedAddCommGroup.coe_neg] at hρ
            norm_cast at *
            omega
  have hfun : (fun s ↦ sLocalNormalizedZFunction f (chartₛ(χ) s)) =
      fun s ↦ toMeromorphicNFOn (fun t ↦ (Z * Λ) (s + t)) univ 0 := by
    funext s
    simp only [sLocalNormalizedZFunction, sLocal_chart_twist, Pi.mul_apply, Z, Λ, div_eq_mul_inv]
  rw [hfun]
  exact analyticOnNhd_toMeromorphicNFOn_translate hH hord

/-- Paper: Equations (3.3.1.31) and (3.3.1.33), pp. 136–137. The entire
normalized zeta functions satisfy the S-local Fourier functional equation.
Deviation: The numerator on the right is the Z-function in (3.3.1.33). -/
theorem sLocalNormalizedZFunction_functionalEquation (f : ℬ(SAdeleRing F S))
    (c : QuasiCharacter Jₛ) :
    sLocalNormalizedZFunction f c =
      sLocalEpsilonFactor c * sLocalNormalizedZFunction (sAdeleSchwartzFourier f)
        (dualQuasiCharacter (G := Jₛ) mₛ hmₛ c) := by
  obtain ⟨χ, t, rfl⟩ := exists_sLocal_chart c
  let G (s : ℂ) := sLocalNormalizedZFunction f (chartₛ(χ) s)
  let H (s : ℂ) := sLocalEpsilonFactor (chartₛ(χ) s) *
    sLocalNormalizedZFunction (sAdeleSchwartzFourier f) (chartₛ(χ⁻¹) (1 - s))
  have hG : AnalyticOnNhd ℂ G univ := sLocalNormalizedZFunction_entire f χ
  have hH : AnalyticOnNhd ℂ H univ := fun s _ ↦ ((sLocalEpsilonFactor_entire χ) s trivial).mul
    (((sLocalNormalizedZFunction_entire (sAdeleSchwartzFourier f) χ⁻¹)
      (1 - s) trivial).comp (f := fun z : ℂ ↦ 1 - z) (by fun_prop))
  have hstrip : ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ), s.re ∈ Ioo (0 : ℝ) 1 :=
    nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds (by
      norm_num [mem_preimage, mem_Ioo]))
  have heq : G =ᶠ[𝓝[≠] (1 / 2 : ℂ)] H := by
    filter_upwards [hstrip, nhdsNE_le_codiscrete _ (sLocalRhoFactor_eq_epsilon_mul χ),
      nhdsNE_le_codiscrete _ (sLocalRhoFactor_mul_dual χ)] with s hs hρ hprod
    let d := chartₛ(χ) s
    let d' := chartₛ(χ⁻¹) (1 - s)
    have hr : sLocalRhoFactor d ≠ 0 := left_ne_zero_of_mul
      (hprod.trans_ne ((Group.isUnit (QuotientGroup.mk (-1 : (SAdeleRing F S)ˣ) : Jₛ)).map d).ne_zero)
    have hz := sLocalIdelicZetaIntegral_functionalEquation f χ s hs
    simp only [sLocal_dual_chart] at hρ hz
    change sLocalRhoFactor d = sLocalEpsilonFactor d * (sLocalHeckeL d / sLocalHeckeL d') at hρ
    change sLocalIdelicZetaIntegral f d = sLocalRhoFactor d *
      sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) d' at hz
    have hL : sLocalHeckeL d ≠ 0 := fun h ↦ hr (by simp [hρ, h])
    have hpos : 1 - s ∈ rightHalf := by
      change 0 < (1 - s).re
      simpa using sub_pos.mpr hs.2
    change sLocalNormalizedZFunction f d = sLocalEpsilonFactor d *
      sLocalNormalizedZFunction (sAdeleSchwartzFourier f) d'
    have hf : sLocalNormalizedZFunction f d = sLocalIdelicZetaIntegral f d / sLocalHeckeL d :=
      sLocalNormalizedZFunction_eq_div f χ hs.1
    have hf' : sLocalNormalizedZFunction (sAdeleSchwartzFourier f) d' =
        sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) d' / sLocalHeckeL d' :=
      sLocalNormalizedZFunction_eq_div (sAdeleSchwartzFourier f) χ⁻¹ hpos
    rw [hf, hf', hz, hρ]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    calc
      _ = (sLocalEpsilonFactor d * (sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) d' *
            (sLocalHeckeL d')⁻¹)) * (sLocalHeckeL d * (sLocalHeckeL d)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hL, mul_one]
  rw [sLocal_dual_chart]
  exact congrFun (hG.eq_of_frequently_eq hH heq.frequently) t

/-- The norm powers of a nonarchimedean local character are periodic in height. -/
private theorem finiteLocal_chart_periodic (v : Primes)
    (η : PontryaginDual (v.adicCompletion F)ˣ) :
    ∃ T : ℝ, 0 < T ∧ Periodic (chart𝔭[v, η]) ((T : ℂ) * Complex.I) := by
  let q := (v.asIdeal.absNorm : ℝ)
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  let T := 2 * Real.pi / Real.log q
  refine ⟨T, div_pos (by positivity) (Real.log_pos hq), fun z ↦ ?_⟩
  ext1 u
  let k := WithZero.log (Valued.v u.val)
  have hnorm : ‖u.val‖ = q ^ k := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _
      ((Valuation.ne_zero_iff _).mpr u.ne_zero)]
    push_cast
    rfl
  have hu : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero
  have hlog : Complex.log (‖u.val‖ : ℂ) = (k : ℂ) * (Real.log q : ℂ) := by
    rw [← Complex.ofReal_log hu.le, hnorm, Real.log_zpow, Complex.ofReal_mul,
      Complex.ofReal_intCast]
  have hprod : (Real.log q : ℂ) * ((T : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * Complex.I := by
    dsimp only [T]
    push_cast
    field_simp [(Real.log_pos hq).ne']
  have hpow : (‖u.val‖ : ℂ) ^ ((T : ℂ) * Complex.I) = 1 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), hlog, mul_assoc, hprod,
      Complex.exp_int_mul_two_pi_mul_I]
  change (η u : ℂ) * (‖u.val‖ : ℂ) ^ (z + (T : ℂ) * Complex.I) =
    (η u : ℂ) * (‖u.val‖ : ℂ) ^ z
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne'), hpow, mul_one]

/-- A continuous function periodic in the imaginary direction is bounded on closed strips. -/
private theorem norm_bounded_on_strip_of_periodic {p : ℂ → ℂ} {T : ℝ}
    (hT : 0 < T) (hperiod : Periodic p ((T : ℂ) * Complex.I))
    (hp : Continuous p) (a b : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → ‖p z‖ ≤ C := by
  let K := Complex.reProdIm (Icc a b) (Icc 0 T)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨C, hC⟩ := hK.bddAbove_image hp.norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z hz ↦ ?_⟩
  let n := ⌊z.im / T⌋
  let v := (n : ℂ) * ((T : ℂ) * Complex.I)
  have hvre : v.re = 0 := by simp [v, Complex.mul_re, Complex.mul_im]
  have hvim : v.im = (n : ℝ) * T := by simp [v, Complex.mul_re, Complex.mul_im]
  have hzK : z - v ∈ K := by
    have hfloor := (le_div_iff₀ hT).mp (Int.floor_le (z.im / T))
    have hceil := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (z.im / T))
    change (z - v).re ∈ Icc a b ∧ (z - v).im ∈ Icc 0 T
    rw [Complex.sub_re, hvre, sub_zero, Complex.sub_im, hvim]
    exact ⟨hz, ⟨by dsimp [n]; linarith, by dsimp [n]; linarith⟩⟩
  have hper : p z = p (z - v) := by
    simpa only [v, zsmul_eq_mul, sub_add_cancel] using (hperiod.zsmul n (z - v))
  rw [hper]
  exact (hC ⟨z - v, hzK, rfl⟩).trans (le_max_left _ _)

/-- The archimedean epsilon factors have norm one, and periodicity of each finite factor
gives a bound for their product on every closed strip. -/
private theorem sLocalEpsilonFactor_bounded_on_strip (χ : PontryaginDual Jₛ) (a b : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → ‖sLocalEpsilonFactor (chartₛ(χ) z)‖ ≤ C := by
  classical
  have hfinite (v : S) : ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b →
      ‖finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z))‖ ≤ C := by
    obtain ⟨η, hη, _⟩ := sLocalFinite_charts χ v
    obtain ⟨T, hT, hperiod⟩ := finiteLocal_chart_periodic v.val η
    have hE : Periodic (finiteLocalEpsilonFactor v.val ∘ chart𝔭[v.val, η])
        ((T : ℂ) * Complex.I) := fun z ↦ congrArg (finiteLocalEpsilonFactor v.val) (hperiod z)
    simpa only [hη, Function.comp_apply] using
      norm_bounded_on_strip_of_periodic hT hE
        (continuous_iff_continuousAt.mpr fun z ↦
          ((finiteLocalEpsilonFactor_entire v.val η) z (mem_univ z)).continuousAt) a b
  choose C hC hbound using hfinite
  refine ⟨∏ v : S, C v, Finset.prod_nonneg fun v _ ↦ hC v, fun z hz ↦ ?_⟩
  have harch (w : InfinitePlace F) :
      ‖infiniteLocalEpsilonFactor w (sLocalInfiniteRestriction w (chartₛ(χ) z))‖ = 1 := by
    unfold infiniteLocalEpsilonFactor
    split <;> rw [norm_pow, Complex.norm_I, one_pow]
  rw [sLocalEpsilonFactor, norm_mul, norm_prod, norm_prod]
  simp only [harch, Finset.prod_const_one, one_mul]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ hbound v z hz)

section ClearedEulerStrips

local notation "G" => SIdeleQuotient F S
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "B" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "cc" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chart(" χ ")" => quasiCharacterNormTwist (sIdeleQuotientNorm F S)
  (isProperMap_sIdeleQuotientNorm F S).continuous ((cc).comp χ)
local notation "Z(" f ", " χ ", " z ")" => sLocalIdelicZFunction f (chart(χ) z)
local notation "Poly(" η ", " z ")" => ∏ v : S, (finiteHeckeEulerFactor η v.val z)⁻¹

private theorem cleared_gamma_bound (η : U) (a : ℝ) :
    ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ 1/2 → T ≤ |z.im| →
      ‖heckeGammaFactor η z / heckeGammaFactor η⁻¹ (1-z)‖ ≤ C := by
  obtain ⟨C,T,hC,_,h⟩ := heckeGamma_reflection_bound η⁻¹ (1/2) (1-a)
  refine ⟨C,max T 1,hC.le,fun z ha hb ht ↦ ?_⟩
  have hre : (1-z).re = 1-z.re := by simp
  have him : |(1-z).im| = |z.im| := by simp
  have hh := h (1-z) (by rw [hre]; linarith) (by rw [hre]; linarith)
    (him ▸ (le_max_left _ _).trans ht)
  rw [inv_inv,sub_sub_cancel,him,hre] at hh
  apply hh.trans
  apply mul_le_of_le_one_right hC.le
  apply Real.rpow_le_one_of_one_le_of_nonpos ((le_max_right _ _).trans ht)
  exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)

private theorem cleared_finite_positive_bound (η : U) :
    ∃ D ≥ (0 : ℝ), ∀ z : ℂ, 0 ≤ z.re → ‖Poly(η,z)‖ ≤ D := by
  classical
  let V (v : S) := 1 + ‖(ideleClassNormTwist η 0).localValue v.val‖
  refine ⟨∏ v, V v, Finset.prod_nonneg (fun v _ ↦ by dsimp [V]; positivity), fun z hz ↦ ?_⟩
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun v _ ↦ norm_nonneg _)
  intro v _
  unfold finiteHeckeEulerFactor
  split_ifs
  · rw [inv_inv]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul]
    have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
    have hpow : ‖(v.val.asIdeal.absNorm : ℂ) ^ (-z)‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hq.le (by simpa using hz)
    exact add_le_add_right (mul_le_of_le_one_right (norm_nonneg _) hpow) _
  · simp [V]

private theorem cleared_finite_continuous (η : U) : Continuous (fun z : ℂ ↦ Poly(η,z)) := by
  classical
  apply continuous_finsetProd
  intro v _
  unfold finiteHeckeEulerFactor
  split_ifs
  · simp only [inv_inv]
    have hq : (v.val.asIdeal.absNorm : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      ((Ideal.absNorm_eq_zero_iff).not.mpr v.val.ne_bot)
    exact continuous_const.sub (continuous_const.mul (continuous_neg.const_cpow (Or.inl hq)))
  · exact continuous_const

private theorem cleared_inverse_factors (χ : PontryaginDual G) (η : U)
    (h : ideleClassNormTwist η 0 ∈ unramifiedOutside F S)
    (he : sIdeleRestriction F S ⟨ideleClassNormTwist η 0,h⟩ = chart(χ) 0) (w : ℂ) :
    sLocalHeckeL (chart(χ⁻¹) w) = heckeGammaFactor η⁻¹ w * ∏ v : S, finiteHeckeEulerFactor η⁻¹ v.val w := by
  have hη (g : IdeleClassGroup (𝓞 F) F) :
      ideleClassNormTwist η⁻¹ 0 g = (ideleClassNormTwist η 0 g)⁻¹ := by
    change (((η g)⁻¹ : Circle) : ℂ) * _ ^ (0 : ℂ) = ((η g : ℂ) * _ ^ (0 : ℂ))⁻¹
    simp
  have hr : ideleClassNormTwist η⁻¹ 0 ∈ unramifiedOutside F S := by
    rw [mem_unramifiedOutside_iff] at h ⊢
    intro v hv u
    have hu := h v hv u
    exact (hη _).trans ((congrArg Inv.inv hu).trans inv_one)
  apply sLocalHeckeL_eq_partialEulerProduct _ _ hr
  ext1 x
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective x
  have hbase := DFunLike.congr_fun he (QuotientGroup.mk g)
  rw [sIdeleRestriction_mk] at hbase ⊢
  rw [hη, hbase]
  change ((χ _ : ℂ) * _ ^ (0 : ℂ))⁻¹ = (((χ _)⁻¹ : Circle) : ℂ) * _ ^ (0 : ℂ)
  simp

private theorem cleared_reflection (χ : PontryaginDual G) (η : U) (f : B)
    (h : ideleClassNormTwist η 0 ∈ unramifiedOutside F S)
    (he : sIdeleRestriction F S ⟨ideleClassNormTwist η 0,h⟩ = chart(χ) 0) :
    ∀ᶠ z : ℂ in codiscrete ℂ, Poly(η,z) * Z(f,χ,z) =
      sLocalEpsilonFactor (chart(χ) z) * (heckeGammaFactor η z / heckeGammaFactor η⁻¹ (1-z)) *
        (Poly(η⁻¹,1-z) * Z(sAdeleSchwartzFourier f,χ⁻¹,1-z)) := by
  have hZ : (fun z ↦ Z(f,χ,z)) =ᶠ[codiscrete ℂ] (fun z ↦ sLocalRhoFactor (chart(χ) z) *
      Z(sAdeleSchwartzFourier f,χ⁻¹,1-z)) := by
    apply sLocal_meromorphic_identity (fun z ↦ ((sLocalIdelicZFunction_meromorphic f χ) (mem_univ z)).meromorphicAt)
      (fun z ↦ (sLocalRhoFactor_meromorphic χ z).mul
        (((sLocalIdelicZFunction_meromorphic (sAdeleSchwartzFourier f) χ⁻¹) (mem_univ (1-z))).meromorphicAt.comp_analyticAt
          (g := fun u : ℂ ↦ 1-u) (by fun_prop)))
    intro z hz
    have hd : 0 < (1 - z).re := by simpa using sub_pos.mpr hz.2
    refine (sLocalIdelicZFunction_eq_integral f ⟨χ,z,hz.1,rfl⟩).trans ?_
    refine (sLocalIdelicZetaIntegral_functionalEquation f χ z hz).trans ?_
    apply congrArg (sLocalRhoFactor (chart(χ) z) * ·)
    exact (congrArg (sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f)) (sLocal_dual_chart χ z)).trans
      (sLocalIdelicZFunction_eq_integral _ ⟨χ⁻¹,1-z,hd,rfl⟩).symm
  filter_upwards [hZ,sLocalRhoFactor_eq_epsilon_mul χ,sLocalRhoFactor_mul_dual χ] with z hz hρ hpair
  have hne : sLocalRhoFactor (chart(χ) z) ≠ 0 := left_ne_zero_of_mul
    (hpair.trans_ne ((Group.isUnit (QuotientGroup.mk (-1 : (SAdeleRing F S)ˣ) : G)).map (chart(χ) z)).ne_zero)
  simp only [sLocal_dual_chart, sLocalHeckeL_eq_partialEulerProduct χ η h he, cleared_inverse_factors χ η h he] at hρ
  have hprod : ∏ v : S, finiteHeckeEulerFactor η v.val z ≠ 0 := by
    intro hh
    exact hne (hρ.trans (by rw [hh, mul_zero, zero_div, mul_zero]))
  rw [hz,hρ]
  simp only [Finset.prod_inv_distrib, div_eq_mul_inv, mul_inv]
  field_simp [hprod]

/-- In the positive half-plane the reciprocal Euler polynomial is bounded. -/
private theorem cleared_positive_height (χ : PontryaginDual G) (η : U) (f : B)
    (b : ℝ) (hb : 1/2 < b) (N : ℕ) :
    ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc (1/2) b → T ≤ |z.im| →
      |z.im| ^ N * ‖Poly(η,z) * Z(f,χ,z)‖ ≤ C := by
  obtain ⟨D,hD,hV⟩ := cleared_finite_positive_bound (S := S) η
  obtain ⟨K,hK,hZ⟩ := sLocalIdelicZFunction_heightBound f χ (1/2) b (by norm_num) hb (N+1) (by omega)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_comap.mp hZ)
  refine ⟨D * K, max T 1, mul_nonneg hD hK.le, fun z hz ht ↦ ?_⟩
  have h1 : 1 ≤ |z.im| := (le_max_right _ _).trans ht
  have hp : 0 < |z.im| := zero_lt_one.trans_le h1
  have hval := hT |z.im| ((le_max_left _ _).trans ht) z.im rfl z.re hz
  rw [Complex.re_add_im] at hval
  have hpow : |z.im| ^ N * ‖Z(f,χ,z)‖ ≤ K := by
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (Nat.le_succ _)) (norm_nonneg _)).trans
      ((le_div_iff₀ (pow_pos hp _)).mp hval)
  rw [norm_mul, mul_left_comm]
  exact mul_le_mul (hV z (by linarith [hz.1])) hpow (by positivity) hD

/-- A uniform bound at large height off a discrete set suffices for a continuous
function, after slightly enlarging the range of real parts. -/
private theorem cleared_extend_bound (q : ℂ → ℂ) (hq : Continuous q) (a b : ℝ)
    (M T : ℝ) (h : ∀ᶠ z : ℂ in codiscrete ℂ,
      z.re ∈ Icc (a-1) (b+1) → T ≤ |z.im| → ‖q z‖ ≤ M) :
    ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖q z‖ ≤ C := by
  have hK := isCompact_Icc (a := a) (b := b) |>.reProdIm (isCompact_Icc (a := -T) (b := T))
  obtain ⟨K,hB⟩ := hK.exists_bound_of_continuousOn hq.continuousOn
  refine ⟨max K M,fun z hz ↦ ?_⟩
  by_cases ht : |z.im| ≤ T
  · exact (hB z ⟨hz,abs_le.mp ht⟩).trans (le_max_left _ _)
  have hnear (z : ℂ) (hz : z.re ∈ Icc a b) (ht : T < |z.im|) : ∀ᶠ w in 𝓝 z,
      w.re ∈ Icc (a-1) (b+1) ∧ T ≤ |w.im| := by
    have h₁ := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show a-1 < z.re by linarith [hz.1])
    have h₂ := (isOpen_lt Complex.continuous_re continuous_const).mem_nhds
      (show z.re < b+1 by linarith [hz.2])
    have h₃ := (isOpen_lt continuous_const Complex.continuous_im.abs).mem_nhds ht
    filter_upwards [h₁,h₂,h₃] with w hw hw' hv
    exact ⟨⟨le_of_lt hw,le_of_lt hw'⟩,le_of_lt hv⟩
  apply (le_max_right K M).trans'
  apply le_of_tendsto ((hq.norm.continuousAt).continuousWithinAt (s := {z}ᶜ))
  filter_upwards [h.filter_mono (nhdsNE_le_codiscrete z),
    (hnear z hz (lt_of_not_ge ht)).filter_mono nhdsWithin_le_nhds] with w hw hnear
  exact hw hnear.1 hnear.2

/-- An entire S-local zeta chart has rapid decay on bounded vertical strips after
multiplication by the finite reciprocal Euler factors of a unitary global lift. -/
theorem sLocalIdelicZFunction_cleared_strips
    (χ : PontryaginDual G) (f : B) (hZ : AnalyticOnNhd ℂ (fun z ↦ Z(f,χ,z)) univ) :
    ∃ η : U, ∀ (a b : ℝ) (N : ℕ), ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b →
      ‖z ^ N * (Poly(η,z) * Z(f,χ,z))‖ ≤ C := by
  obtain ⟨η,h,he,_⟩ := sLocal_character_extension χ
  refine ⟨η,fun a b N ↦ ?_⟩
  let m := 3 + |a| + |b|
  have hm : 1/2 < m := by dsimp only [m]; linarith [abs_nonneg a,abs_nonneg b]
  obtain ⟨C,T,hC,hp⟩ := cleared_positive_height χ η f m hm N
  obtain ⟨D,T',hD,hd⟩ := cleared_positive_height χ⁻¹ η⁻¹ (sAdeleSchwartzFourier f) m hm N
  obtain ⟨A,Tg,hA,hg⟩ := cleared_gamma_bound η (a-1)
  obtain ⟨E,hE,heps⟩ := sLocalEpsilonFactor_bounded_on_strip χ (a - 1) (b + 1)
  let T₀ := max (max T T') (max Tg (max m 1))
  let Q (z : ℂ) := z ^ N * (Poly(η,z) * Z(f,χ,z))
  have hQ : Continuous Q := (continuous_id.pow N).mul
    ((cleared_finite_continuous (S := S) η).mul (continuous_iff_continuousAt.mpr fun z ↦ (hZ z trivial).continuousAt))
  apply cleared_extend_bound Q hQ a b (2 ^ N * max C (E * A * D)) T₀
  filter_upwards [cleared_reflection χ η f h he] with z hz
  intro hr ht
  have ht₁ : T ≤ |z.im| := (le_max_left T T').trans ((le_max_left _ _).trans ht)
  have ht₂ : T' ≤ |z.im| := (le_max_right T T').trans ((le_max_left _ _).trans ht)
  have ht₃ : Tg ≤ |z.im| := (le_max_left Tg _).trans ((le_max_right _ _).trans ht)
  have ht₄ : m ≤ |z.im| := (le_max_left m _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have hweighted : |z.im| ^ N * ‖Poly(η,z) * Z(f,χ,z)‖ ≤ max C (E * A * D) := by
    by_cases hh : 1/2 ≤ z.re
    · exact (hp z ⟨hh, by dsimp only [m]; linarith [hr.2, le_abs_self b, abs_nonneg a]⟩ ht₁).trans (le_max_left _ _)
    · have hw : (1-z).re ∈ Icc (1/2) m := by
        change 1/2 ≤ 1-z.re ∧ 1-z.re ≤ m
        dsimp only [m]; constructor <;> linarith [hr.1, neg_abs_le a, abs_nonneg b]
      have him : |(1-z).im| = |z.im| := by simp
      have hhD := hd (1-z) hw (him ▸ ht₂)
      rw [him] at hhD
      rw [hz,norm_mul,norm_mul,mul_left_comm]
      exact (mul_le_mul (mul_le_mul (heps z hr) (hg z hr.1 (le_of_not_ge hh) ht₃)
        (norm_nonneg _) hE) hhD (by positivity) (mul_nonneg hE hA)).trans (le_max_right _ _)
  have hnorm : ‖z‖ ≤ 2 * |z.im| := by
    apply z.norm_le_abs_re_add_abs_im.trans
    have : |z.re| ≤ m := by
      rw [abs_le]; dsimp only [m]
      constructor <;> linarith [hr.1, hr.2, neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
    linarith
  change ‖z ^ N * _‖ ≤ _
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (2 * |z.im|)^N * ‖Poly(η,z) * Z(f,χ,z)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm N) (norm_nonneg _)
    _ = 2 ^ N * (|z.im| ^ N * ‖Poly(η,z) * Z(f,χ,z)‖) := by rw [mul_pow,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left hweighted (by positivity)

end ClearedEulerStrips

end RiemannMasullo
