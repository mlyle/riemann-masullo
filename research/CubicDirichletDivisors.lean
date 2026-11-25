module

import Lean
public import RiemannMasullo.Ch13_ZerosHecke.Targets
import all RiemannMasullo.ForMathlib.NumberTheory.NumberField.DedekindZeta.MultipleZero
public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import all RiemannMasullo.AppA_AlgebraicNT.Sec2

/-! # Dirichlet twists of the cubic Artin divisor

For the splitting field of `X³ − 2`, the finite-lines hypothesis in
Proposition 10.2.2.2, pp. 446–447 (#7453), forces one finite set of vertical
lines for the positive divisors of *all* Dirichlet twists of the cubic
quotient. Taking the complementary order hypothesis (#7220) bounds the
positive multiplicities by half the order bound on the splitting field.

The unconditional statement `norm_twist_order_relation` works for every
rational unitary Hecke character and every rational S₃ extension. Its
pullbacks use the determinant norm on adele units. All four global functions
in the identity are the repository's meromorphic completed Hecke L-functions.
The primitive-character corollary uses Mathlib's uncompleted Dirichlet L-function
as denominator and the finite Hecke continuation as numerator.

The prime-count identity is from the repository's `DedekindZeta.MultipleZero`.
The two vertical chart lemmas below are taken from ianitstoday's Gap7220.lean,
commit d2790534500584c8751702eb1a0f92cb9aed0239, lines 75–122. Yidakra
described the common induction formula in the discussion of #7220. Marcopetterson
independently gave the conductor-uniform consequence in issue #7453 on 24
November. The proof here verifies the arithmetic consequence in Lean.

The final checks collect kernel axioms and also traverse every dependency in
the statement and proof of each listed result.
-/

open NumberField IsDedekindDomain Set Filter Function Topology
open scoped NumberField.AdeleRing RestrictedProduct Topology
public noncomputable section
namespace RiemannMasullo
namespace TwistedCubic
set_option quotPrecheck false

local notation "U[" E "]" => PontryaginDual (IdeleClassGroup (𝓞 E) E)
local notation "Pr[" E "]" => HeightOneSpectrum (𝓞 E)

private def coefficient {E : Type} [Field E] [NumberField E] (χ : U[E]) (v : Pr[E]) : ℂ :=
  open Classical in
  if (ideleClassNormTwist χ 0).IsUnramifiedAt v then (ideleClassNormTwist χ 0).localValue v else 0

private def factor (c : ℂ) (n : ℕ) (s : ℂ) := 1 - c * (n : ℂ) ^ (-s)

private theorem coeff_bound {E : Type} [Field E] [NumberField E] (χ : U[E]) (v : Pr[E]) :
    ‖coefficient χ v‖ ≤ 1 := by
  classical
  unfold coefficient
  split_ifs <;> simp [norm_ideleClassNormTwist_zero_localValue]

private theorem nonzero_factor (c : ℂ) (hc : ‖c‖ ≤ 1) (n : ℕ) (hn : 1 < n)
    (s : ℂ) (hs : 0 < s.re) : factor c n s ≠ 0 := by
  have h : ‖(n : ℂ) ^ (-s)‖ < 1 := by
    change ‖((n : ℝ) : ℂ) ^ (-s)‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < (n : ℝ)), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (neg_lt_zero.mpr hs)
  have hc' : ‖c * (n : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans_lt h
  intro hf
  have he : c * (n : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hf).symm
  rw [he,norm_one] at hc'
  exact hc'.false

private def count (E : Type) [Field E] [NumberField E] (n : ℕ) : ℕ :=
  Nat.card {v : Pr[E] // v.asIdeal.absNorm = n}

private theorem grouped_removed {E : Type} [Field E] [NumberField E] (χ : U[E])
    (w : ℕ → ℂ) (B : Finset ℕ)
    (hχ : ∀ v : Pr[E], v.asIdeal.absNorm ∉ B → coefficient χ v = w v.asIdeal.absNorm) :
    ∃ P : ℂ → ℂ, AnalyticOnNhd ℂ P univ ∧ (∀ s : ℂ, 0 < s.re → P s ≠ 0) ∧
      ∀ (s : ℂ) (hs : 1 < s.re), HasProd
        (fun n : ℕ ↦ (if n ∈ B then 1 else (factor (w n) n s)⁻¹) ^ count E n)
        (finiteHeckeL χ ⟨s, hs⟩ * P s) := by
  classical
  let u := fun v : Pr[E] ↦ v.asIdeal.absNorm
  have hfinite (n : ℕ) : {v : Pr[E] | u v = n}.Finite := by
    exact (Ring.HasFiniteQuotients.finite_absNorm_eq n).preimage
      (fun _ _ _ _ h ↦ HeightOneSpectrum.ext h)
  let T := B.biUnion fun n ↦ (hfinite n).toFinset
  have hT (v : Pr[E]) : v ∈ T ↔ u v ∈ B := by simp [T]
  let d (v : Pr[E]) (s : ℂ) := factor (coefficient χ v) (u v) s
  let P (s : ℂ) := ∏ v ∈ T, d v s
  have hd (v : Pr[E]) (s : ℂ) (hs : 0 < s.re) : d v s ≠ 0 :=
    nonzero_factor _ (coeff_bound χ v) _ (NumberField.HeightOneSpectrum.one_lt_absNorm v) s hs
  refine ⟨P, ?_, fun s hs ↦ Finset.prod_ne_zero_iff.mpr (fun v _ ↦ hd v s hs), ?_⟩
  · intro s _
    apply Differentiable.analyticAt
    apply Differentiable.fun_finsetProd
    intro v _
    have hev : (u v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
    exact (differentiable_const (1 : ℂ)).sub ((differentiable_const (coefficient χ v)).mul (differentiable_id.neg.const_cpow (Or.inl hev)))
  intro s hs
  have hlocal (v : Pr[E]) : finiteHeckeEulerFactor χ v s = (d v s)⁻¹ := by
    simp only [finiteHeckeEulerFactor, d, factor, coefficient, u]
    split_ifs <;> simp
  have hp : HasProd (fun v ↦ if v ∈ T then d v s else 1) (P s) := by
    have he : HasProd (fun v ↦ if v ∈ T then d v s else 1)
        (∏ v ∈ T, if v ∈ T then d v s else 1) := hasProd_prod_of_ne_finset_one (s := T)
      (f := fun v ↦ if v ∈ T then d v s else 1) (fun v hv ↦ by simp [hv])
    simpa [P] using he
  let g n := if n ∈ B then (1 : ℂ) else (factor (w n) n s)⁻¹
  have hprod : HasProd (fun v : Pr[E] ↦ g (u v)) (finiteHeckeL χ ⟨s, hs⟩ * P s) := by
    apply ((finiteHeckeL_hasProd χ ⟨s,hs⟩).mul hp).congr_fun
    intro v
    change g (u v) = finiteHeckeEulerFactor χ v s * _
    rw [hlocal]
    by_cases h : u v ∈ B
    · simp [g, h, (hT v).mpr h, hd v s (zero_lt_one.trans hs)]
    · simp [g, h, mt (hT v).mp h, d, hχ v h]
      rfl
  let e := Equiv.sigmaFiberEquiv u
  apply (e.hasProd_iff.mpr hprod).sigma
  intro n
  have : Finite {v // u v = n} := (hfinite n).to_subtype
  let := Fintype.ofFinite {v // u v = n}
  convert hasProd_fintype (fun _ : {v // u v = n} ↦ g n) using 1
  · ext v
    change g (u v.val) = _
    rw [v.property]
  · rw [Finset.prod_const, Finset.card_univ]
    exact congrArg _ (Nat.card_eq_fintype_card (α := {v // u v = n}))

private def continuation {E : Type} [Field E] [NumberField E] (χ : U[E]) : ℂ → ℂ :=
  (finiteHeckeL_exists_continuation χ).choose

private theorem corrected_order {E : Type} [Field E] [NumberField E]
    (χ : U[E]) (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ)
    (hn : ∀ s : ℂ, 0 < s.re → P s ≠ 0) {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt (continuation χ * P) z = meromorphicOrderAt (continuedCompletedHeckeL χ) z := by
  have hf := (finiteHeckeL_exists_continuation χ).choose_spec
  have hP₀ := (hP z (mem_univ _)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hn z hz)
  unfold continuation
  rw [meromorphicOrderAt_mul (hf.1 (mem_univ z)).meromorphicAt (hP z (mem_univ _)).meromorphicAt,
    hP₀, add_zero]
  exact meromorphicOrderAt_finiteHeckeL_continuation χ hf.1.meromorphicOn hf.2 hz

/-- An S₃ field, its quadratic and cubic subfields, and ℚ satisfy the
Brauer order identity for all four genuine Hecke characters whose good
Euler coefficients have the same norm weight. Both the finite exceptional
set and the weight may depend on the four characters. -/
private theorem common_weight_order_relation
    (L k K : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    [Field k] [NumberField k] [Field K] [NumberField K]
    (hG : Nonempty ((L ≃ₐ[ℚ] L) ≃* Equiv.Perm (Fin 3)))
    (ιk : Nonempty (k →ₐ[ℚ] L)) (hkdeg : Module.finrank ℚ k = 2)
    (ιK : Nonempty (K →ₐ[ℚ] L)) (hKdeg : Module.finrank ℚ K = 3)
    (χL : U[L]) (χ₀ : U[ℚ]) (χk : U[k]) (χK : U[K])
    (w : ℕ → ℂ) (B : Finset ℕ)
    (hL : ∀ v : Pr[L], v.asIdeal.absNorm ∉ B → coefficient χL v = w v.asIdeal.absNorm)
    (h₀ : ∀ v : Pr[ℚ], v.asIdeal.absNorm ∉ B → coefficient χ₀ v = w v.asIdeal.absNorm)
    (hk : ∀ v : Pr[k], v.asIdeal.absNorm ∉ B → coefficient χk v = w v.asIdeal.absNorm)
    (hK : ∀ v : Pr[K], v.asIdeal.absNorm ∉ B → coefficient χK v = w v.asIdeal.absNorm)
    {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt (continuedCompletedHeckeL χL) z +
      (2 : ℕ) * meromorphicOrderAt (continuedCompletedHeckeL χ₀) z =
    meromorphicOrderAt (continuedCompletedHeckeL χk) z +
      (2 : ℕ) * meromorphicOrderAt (continuedCompletedHeckeL χK) z := by
  classical
  obtain ⟨A, -, hA⟩ := spectralLineJet_memLp_false_primeCounts L k K hG ιk hkdeg ιK hKdeg
  let T := A ∪ B
  have hB {n : ℕ} (hn : n ∉ T) : n ∉ B := fun h ↦ hn (Finset.mem_union_right _ h)
  obtain ⟨P, hp, hpn, hPe⟩ := grouped_removed χL w T (fun v hv ↦ hL v (hB hv))
  obtain ⟨Q, hq, hqn, hQe⟩ := grouped_removed χ₀ w T (fun v hv ↦ h₀ v (hB hv))
  obtain ⟨U, hu, hun, hUe⟩ := grouped_removed χk w T (fun v hv ↦ hk v (hB hv))
  obtain ⟨V, hv, hvn, hVe⟩ := grouped_removed χK w T (fun v hv ↦ hK v (hB hv))
  have hm {E : Type} [Field E] [NumberField E] (χ : U[E]) (W : ℂ → ℂ)
      (hW : AnalyticOnNhd ℂ W univ) : MeromorphicOn (continuation χ * W) univ :=
    (finiteHeckeL_exists_continuation χ).choose_spec.1.meromorphicOn.mul hW.meromorphicOn
  have he := meromorphicContinuation_eventuallyEq
    ((hm χL P hp).mul ((hm χ₀ Q hq).pow 2))
    ((hm χk U hu).mul ((hm χK V hv).pow 2)) (fun s hs ↦ ?_) z
  · have h := meromorphicOrderAt_congr he
    rw [meromorphicOrderAt_mul ((hm χL P hp) z (mem_univ _)) (((hm χ₀ Q hq) z (mem_univ _)).pow 2),
      meromorphicOrderAt_mul ((hm χk U hu) z (mem_univ _)) (((hm χK V hv) z (mem_univ _)).pow 2),
      meromorphicOrderAt_pow ((hm χ₀ Q hq) z (mem_univ _)),
      meromorphicOrderAt_pow ((hm χK V hv) z (mem_univ _)),
      corrected_order χL P hp hpn hz, corrected_order χ₀ Q hq hqn hz,
      corrected_order χk U hu hun hz, corrected_order χK V hv hvn hz] at h
    exact h
  · have HC {E : Type} [Field E] [NumberField E] (χ : U[E]) :
        continuation χ s = finiteHeckeL χ ⟨s,hs⟩ := (finiteHeckeL_exists_continuation χ).choose_spec.2 ⟨s,hs⟩
    simp only [Pi.mul_apply, Pi.pow_apply, HC]
    refine (((hPe s hs).mul ((hQe s hs).pow 2)).congr_fun (fun n ↦ ?_)).unique
      ((hUe s hs).mul ((hVe s hs).pow 2))
    by_cases hn : n ∈ T
    · simp [hn]
    · have hc : count L n + 2 * count ℚ n = count k n + 2 * count K n :=
        hA n (fun h ↦ hn (Finset.mem_union_left _ h))
      simp only [← pow_mul, ← pow_add, mul_comm _ 2, hc]
local notation "𝕀[" E "]" => IdeleGroup (𝓞 E) E
local notation "C[" E "]" => IdeleClassGroup (𝓞 E) E
local notation "princ(" E ")" => IdeleGroup.principalSubgroup (𝓞 E) E
variable (E : Type) [Field E] [NumberField E]

private theorem norm_principal :
    princ(E) ≤ (princ(ℚ)).comap (relativeIdeleNormRat E) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨Units.map (Algebra.norm ℚ) x, Units.ext ?_⟩
  obtain ⟨b, hb⟩ := exists_adelicIntegralBasis E
  exact (rationalAdeleNorm_diagonal E b hb (x : E)).symm

/-- The determinant norm on ideles descends continuously to their class groups. -/
def classNorm : C[E] →ₜ* C[ℚ] where
  toMonoidHom := QuotientGroup.map (princ(E)) (princ(ℚ)) (relativeIdeleNormRat E) (norm_principal E)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk (princ(E))).continuous_iff.mpr <|
    (QuotientGroup.isQuotientMap_mk (princ(ℚ))).continuous.comp (relativeIdeleNormRat_continuous E)

private def finitePart (v : Pr[ℚ]) (x : 𝕀[ℚ]) : (v.adicCompletion ℚ)ˣ :=
  Units.map ((RestrictedProduct.evalRingHom (fun w : Pr[ℚ] ↦ w.adicCompletion ℚ) v).comp
    (RingHom.snd _ _)).toMonoidHom x

private theorem norm_local (v : Pr[E]) (x : (v.adicCompletion E)ˣ) :
    let p := v.under (𝓞 ℚ)
    let a := IdeleGroup.ofAdicCompletion (𝓞 E) E v x
    let b := relativeIdeleNormRat E a
    b = IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ p (finitePart p b) ∧
      ‖((finitePart p b : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)‖ = ‖(x : v.adicCompletion E)‖ := by
  classical
  intro p a b
  let t : 𝔸ᶠ[ℚ] := ⟨Pi.single p 1, by
    filter_upwards [Filter.eventually_cofinite_ne p] with w hw
    rw [Pi.single_eq_of_ne hw]
    exact (w.adicCompletionIntegers ℚ).zero_mem⟩
  let r : 𝔸[ℚ] := 1 - (0,t)
  have hrp : r.2 p = 0 := by
    change 1 - Pi.single p (1 : p.adicCompletion ℚ) p = 0
    rw [Pi.single_eq_same,sub_self]
  have hev := (rationalAdeleEmbedding_spec E).2.2.2 p v rfl r hrp
  have hlocal : rationalAdeleEmbedding E r * a.val = rationalAdeleEmbedding E r := by
    refine Prod.ext ?_ ?_
    · change _ * (1 : InfiniteAdeleRing E) = _
      rw [mul_one]
    · apply FiniteAdeleRing.ext
      intro w
      change (rationalAdeleEmbedding E r).2 w * Pi.mulSingle v (x : v.adicCompletion E) w = _
      by_cases h : w = v
      · subst w
        rw [hev, zero_mul]
      · rw [Pi.mulSingle_eq_of_ne h, mul_one]
  let := (rationalAdeleEmbedding E).toAlgebra
  obtain ⟨basis⟩ := rationalAdeleEmbedding_hasBasis E
  have hn := congrArg (Algebra.norm 𝔸[ℚ]) hlocal
  rw [map_mul, show Algebra.norm 𝔸[ℚ] (rationalAdeleEmbedding E r) =
      r ^ Module.finrank ℚ E by
    rw [show rationalAdeleEmbedding E r = algebraMap 𝔸[ℚ] 𝔸[E] r by rfl]
    simpa only [Fintype.card_fin] using Algebra.norm_algebraMap_of_basis basis r] at hn
  change r ^ Module.finrank ℚ E * b.val = r ^ Module.finrank ℚ E at hn
  constructor
  · apply Units.ext
    refine Prod.ext ?_ ?_
    · have h := congrArg Prod.fst hn
      change ((1 : InfiniteAdeleRing ℚ) - 0) ^ _ * b.val.1 = ((1 : InfiniteAdeleRing ℚ) - 0) ^ _ at h
      simpa using h
    · apply FiniteAdeleRing.ext
      intro w
      change b.val.2 w = Pi.mulSingle p ((finitePart p b : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) w
      by_cases hw : w = p
      · subst w
        rw [Pi.mulSingle_eq_same]
        rfl
      · rw [Pi.mulSingle_eq_of_ne hw]
        have h := congrArg (fun y : 𝔸[ℚ] ↦ y.2 w) hn
        change (1 - Pi.single p (1 : p.adicCompletion ℚ) w) ^ _ * b.val.2 w =
          (1 - Pi.single p (1 : p.adicCompletion ℚ) w) ^ _ at h
        simpa [Pi.single_eq_of_ne hw] using h
  · change ‖(Algebra.norm 𝔸[ℚ] a.val).2 p‖ = _
    rw [rationalAdeleNorm_finitePlace E p a.val]
    calc
      _ = ∏ w ∈ (finite_finitePlacesOver_rat E p).toFinset, ‖a.val.2 w‖ :=
        finprod_mem_eq_finite_toFinset_prod _ (finite_finitePlacesOver_rat E p)
      _ = _ := ?_
    have hv : v ∈ (finite_finitePlacesOver_rat E p).toFinset := by simp [p]
    rw [Finset.prod_eq_single_of_mem v hv]
    · change ‖Pi.mulSingle v (x : v.adicCompletion E) v‖ = _
      rw [Pi.mulSingle_eq_same]
    · intro w _ hw
      change ‖Pi.mulSingle v (x : v.adicCompletion E) w‖ = 1
      rw [Pi.mulSingle_eq_of_ne hw,norm_one]

private def localAngular {E : Type} [Field E] [NumberField E]
    (v : Pr[E]) (ψ : U[E]) (x : (v.adicCompletion E)ˣ) : Circle :=
  ψ (IdeleClassGroup.ofAdicCompletion (𝓞 E) E v x)

private theorem unram_iff {E : Type} [Field E] [NumberField E] (v : Pr[E]) (ψ : U[E]) :
    (ideleClassNormTwist ψ 0).IsUnramifiedAt v ↔
      ∀ x : (v.adicCompletion E)ˣ, ‖x.val‖ = 1 → localAngular v ψ x = 1 :=
  finiteUnitary_unramified v ψ

def normPullback (ψ : U[ℚ]) := ψ.comp (classNorm E)

private theorem pull_local (v : Pr[E]) (ψ : U[ℚ]) (x : (v.adicCompletion E)ˣ) :
    let p := v.under (𝓞 ℚ)
    let y := finitePart p (relativeIdeleNormRat E (IdeleGroup.ofAdicCompletion (𝓞 E) E v x))
    localAngular v (normPullback E ψ) x = localAngular p ψ y ∧ ‖y.val‖ = ‖x.val‖ := by
  intro p y
  obtain ⟨he, hn⟩ := norm_local E v x
  refine ⟨?_,hn⟩
  exact congrArg (fun g : 𝕀[ℚ] ↦ ψ (QuotientGroup.mk g)) he

private theorem pull_unram (v : Pr[E]) (ψ : U[ℚ])
    (h : (ideleClassNormTwist ψ 0).IsUnramifiedAt (v.under (𝓞 ℚ))) :
    (ideleClassNormTwist (normPullback E ψ) 0).IsUnramifiedAt v := by
  apply (unram_iff _ _).mpr
  intro x hx
  obtain ⟨he,hn⟩ := pull_local E v ψ x
  exact he.trans ((unram_iff _ _).mp h _ (hn.trans hx))

private theorem minFac_norm (v : Pr[E]) :
    v.asIdeal.absNorm.minFac = (Rat.HeightOneSpectrum.primesEquiv (v.under (𝓞 ℚ))).val := by
  let p := v.under (𝓞 ℚ)
  have : v.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have hc := Ideal.absNorm_pow_inertiaDeg p.asIdeal v.asIdeal
  have hp := spectralLineJet_memLp_false_ratNorm p
  have hpos : v.asIdeal.inertiaDeg (𝓞 ℚ) ≠ 0 := by
    intro hn
    rw [hn, pow_zero] at hc
    exact (NumberField.HeightOneSpectrum.one_lt_absNorm v).ne hc
  rw [← hc, hp]
  exact (Rat.HeightOneSpectrum.primesEquiv p).property.pow_minFac hpos

/-- A norm n determines its underlying rational prime and a norm shell there.
At unramified rational primes a unitary Hecke character takes a single value
on this shell. For n not represented by such a shell its chosen value is immaterial. -/
private def weight (ψ : U[ℚ]) (n : ℕ) : ℂ := open Classical in
  let C (z : Circle) := ∃ (p : Pr[ℚ]) (x : (p.adicCompletion ℚ)ˣ),
    (Rat.HeightOneSpectrum.primesEquiv p).val = n.minFac ∧
      ‖x.val‖ = (n : ℝ)⁻¹ ∧ z = localAngular p ψ x
  if h : ∃ z, C z then (h.choose : ℂ) else 0

private theorem weight_eq (ψ : U[ℚ]) (n : ℕ) (p : Pr[ℚ]) (x : (p.adicCompletion ℚ)ˣ)
    (hp : (Rat.HeightOneSpectrum.primesEquiv p).val = n.minFac) (hx : ‖x.val‖ = (n : ℝ)⁻¹)
    (hu : (ideleClassNormTwist ψ 0).IsUnramifiedAt p) : weight ψ n = (localAngular p ψ x : ℂ) := by
  classical
  unfold weight
  dsimp only
  split_ifs with h
  · obtain ⟨q, y, hq, hy, he⟩ := h.choose_spec
    have hqp : q = p := Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext (hq.trans hp.symm))
    subst q
    rw [he]
    have hn : ‖(y / x).val‖ = 1 := by
      rw [Units.val_div_eq_div_val, norm_div, hy, ← hx, div_self (norm_ne_zero_iff.mpr x.ne_zero)]
    have ht := (unram_iff _ _).mp hu _ hn
    change ψ ((IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ p) (y / x)) = 1 at ht
    rw [map_div, map_div, div_eq_one] at ht
    exact congrArg ((↑) : Circle → ℂ) ht
  · exact False.elim (h ⟨_,p,x,hp,hx,rfl⟩)

private theorem good_coefficient (v : Pr[E]) (ψ : U[ℚ])
    (h : (ideleClassNormTwist ψ 0).IsUnramifiedAt (v.under (𝓞 ℚ))) :
    coefficient (normPullback E ψ) v = weight ψ v.asIdeal.absNorm := by
  classical
  let val := (Valued.v : Valuation (v.adicCompletion E) (WithZero (Multiplicative ℤ)))
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let x := Units.mk0 (π : v.adicCompletion E) hπ.ne_zero
  let p := v.under (𝓞 ℚ)
  let y := finitePart p (relativeIdeleNormRat E (IdeleGroup.ofAdicCompletion (𝓞 E) E v x))
  obtain ⟨he,hn⟩ := pull_local E v ψ x
  rw [weight_eq ψ _ p y (minFac_norm E v).symm
    (hn.trans (norm_uniformizer_adicCompletion v (π : v.adicCompletion E) hπ)) h]
  have hu := pull_unram E v ψ h
  unfold coefficient
  rw [ite_eq_left hu, hu.localValue_eq _ hπ]
  change (ideleClassNormTwist (normPullback E ψ) 0).restrict v (x.val) = _
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  change (localAngular v (normPullback E ψ) x : ℂ) * _ ^ (0 : ℂ) = _
  rw [Complex.cpow_zero, mul_one, he]

private theorem good_norms (T : Finset (Pr[ℚ])) :
    ∃ B : Finset ℕ, ∀ v : Pr[E], v.asIdeal.absNorm ∉ B → v.under (𝓞 ℚ) ∉ T := by
  classical
  let b (p : Pr[ℚ]) := ((finite_finitePlacesOver_rat E p).toFinset).image fun v ↦ v.asIdeal.absNorm
  refine ⟨T.biUnion b, fun v hv hp ↦ hv (Finset.mem_biUnion.mpr ⟨_,hp,?_⟩)⟩
  exact Finset.mem_image.mpr ⟨v, (finite_finitePlacesOver_rat E _).mem_toFinset.mpr rfl, rfl⟩
private theorem pull_rat (ψ : U[ℚ]) : normPullback ℚ ψ = ψ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, extensions⟩ := adele_additive_quotient ℚ
  have h : rationalAdeleEmbedding ℚ = RingHom.id 𝔸[ℚ] :=
    (extensions ℚ (RingHom.id ℚ)).1.unique
      (rationalAdeleEmbedding_spec ℚ) (isAdeleExtension_id ℚ)
  ext1 c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  change ψ (QuotientGroup.mk (relativeIdeleNormRat ℚ x)) = ψ (QuotientGroup.mk x)
  apply congrArg (fun g : 𝕀[ℚ] ↦ ψ (QuotientGroup.mk g))
  simpa [h] using relativeIdeleNormRat_on_rational ℚ x

/-- Artin's S₃ order relation for the pullbacks of every rational unitary Hecke
character, including its ramified twists. No hypothesis on local coefficients
or the conductor remains. -/
theorem norm_twist_order_relation
    (L k K : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    [Field k] [NumberField k] [Field K] [NumberField K]
    (hG : Nonempty ((L ≃ₐ[ℚ] L) ≃* Equiv.Perm (Fin 3)))
    (ιk : Nonempty (k →ₐ[ℚ] L)) (hkdeg : Module.finrank ℚ k = 2)
    (ιK : Nonempty (K →ₐ[ℚ] L)) (hKdeg : Module.finrank ℚ K = 3)
    (ψ : U[ℚ]) {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt (continuedCompletedHeckeL (normPullback L ψ)) z +
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
    (normPullback L ψ) (normPullback ℚ ψ) (normPullback k ψ) (normPullback K ψ) (weight ψ) B
    (fun v hv ↦ good_coefficient L v ψ (hT _ (hl v (hsub _ hv).1.1)))
    (fun v hv ↦ good_coefficient ℚ v ψ (hT _ (ha v (hsub _ hv).1.2)))
    (fun v hv ↦ good_coefficient k v ψ (hT _ (hb v (hsub _ hv).2.1)))
    (fun v hv ↦ good_coefficient K v ψ (hT _ (hc v (hsub _ hv).2.2))) hz
  simpa only [pull_rat] using H

private theorem strip_order {E : Type} [Field E] [NumberField E] (ψ : U[E]) (z : ℂ)
    (h₀ : 0 < z.re) (h₁ : z.re < 1) :
    let o := meromorphicOrderAt (continuedCompletedHeckeL ψ) z
    o = (o.untop₀.toNat : WithTop ℤ) := by
  intro o
  let f := continuedCompletedHeckeL ψ
  have h := continuedCompletedHeckeL_spec ψ
  have hf₂ : f 2 ≠ 0 := by
    change continuedCompletedHeckeL ψ 2 ≠ 0
    rw [show continuedCompletedHeckeL ψ 2 = completedHeckeL ψ ⟨2, by norm_num⟩ from h.2 ⟨2,_⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos ψ (by norm_num))
      (finiteHeckeL_ne_zero_of_one_lt_re ψ ⟨2,by norm_num⟩)
  have ht := h.1.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ z) (by
      rw [(h.1 (mem_univ 2)).meromorphicOrderAt_eq_zero_iff.mpr hf₂]; exact WithTop.coe_ne_top)
  have han : AnalyticAt ℂ f z := by
    by_cases hk : ψ.toMonoidHom.comp (ideleClassNorm E).ker.subtype = 1
    · obtain ⟨t, ⟨_, _, _, ha⟩, _⟩ := completedHeckeL_continuation_simplePoles ψ f h.1 h.2 hk
      apply ha
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      constructor <;> intro he <;> have := congrArg Complex.re he <;>
        simp [Complex.add_re, Complex.mul_re] at this <;> linarith
    · exact (completedHeckeL_continuation_entire ψ f h.1 h.2 hk).analyticAt _
  have hp : 0 ≤ o := han.meromorphicOrderAt_nonneg
  change o ≠ ⊤ at ht
  rw [← WithTop.coe_untop₀_of_ne_top ht] at hp ⊢
  simp only [WithTop.untop₀_coe, ← WithTop.coe_zero, WithTop.coe_le_coe] at hp ⊢
  exact_mod_cast (Int.toNat_of_nonneg hp).symm
section Charts
set_option quotPrecheck false
variable {F : Type} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "multiplicity(" χ ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

-- These two chart lemmas follow @ianitstoday's Gap7220.lean, d279053, lines 75–122.
private theorem order_of_normTwist (ψ θ : PontryaginDual C𝔽) (a : ℂ) (ha : a.re = 0)
    (hψ : ideleClassNormTwist ψ 0 = ideleClassNormTwist θ a) {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (continuedCompletedHeckeL ψ) s =
      meromorphicOrderAt (continuedCompletedHeckeL θ) (s + a) := by
  obtain ⟨g, hg, hgeq⟩ := finiteHeckeL_exists_continuation θ
  have hsa : 0 < (s + a).re := by rw [Complex.add_re, ha, add_zero]; exact hs
  have h1 := meromorphicOrderAt_finiteHeckeL_continuation θ hg.meromorphicOn hgeq hsa
  have hf : MeromorphicOn (g ∘ (fun w : ℂ ↦ w + a)) univ := fun z _ ↦
    MeromorphicAt.comp_analyticAt (f := g) (g := fun w : ℂ ↦ w + a) (x := z)
      (hg.meromorphicOn (z + a) (mem_univ _)) (by fun_prop)
  have h2 := meromorphicOrderAt_finiteHeckeL_continuation ψ hf (fun z ↦ by
    change g ((z : ℂ) + a) = finiteHeckeL ψ z
    rw [finiteHeckeL_imaginary_twist θ ψ a ha hψ z]
    exact hgeq (⟨(z : ℂ) + a, _⟩ : halfPlane)) hs
  rw [← h2, ← h1]
  exact meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (f := g) (c := a) (x := s)

/-- Every unitary character of the idele class group has the zeros of the chosen base point
of its component, moved vertically. -/
private theorem order_eq_basepoint' {χ : PontryaginDual C₁ → PontryaginDual C𝔽}
    (hχ : IsSpectralBasepointChoice χ) (ψ : PontryaginDual C𝔽) :
    ∃ τ : ℝ, ∀ σ t : ℝ, 0 < σ →
      meromorphicOrderAt (continuedCompletedHeckeL ψ) (shift(σ, t)) =
        meromorphicOrderAt (continuedCompletedHeckeL (χ (ψ.comp restriction)))
          (shift(σ, (t + τ : ℝ))) := by
  let ω : PontryaginDual C₁ := ψ.comp restriction
  obtain ⟨z, hz, -⟩ := hχ.existsUnique_normTwist ω (ideleClassNormTwist ψ 0) (fun g ↦ by
    change (ψ g.val : ℂ) * _ ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
    rfl)
  have hre : z.re = 0 := by
    have h1 := quasiCharacterAbscissa_ideleClassNormTwist ψ 0
    have h2 := quasiCharacterAbscissa_ideleClassNormTwist (χ ω) z
    rw [← hz, h1] at h2
    simpa using h2.symm
  refine ⟨z.im, fun σ t hσ ↦ ?_⟩
  have hs : 0 < (shift(σ, t)).re := by simpa using hσ
  rw [order_of_normTwist ψ (χ ω) z hre hz hs]
  congr 1
  apply Complex.ext <;> simp [hre]

/-- The same, without naming the component. -/
private theorem order_eq_basepoint {χ : PontryaginDual C₁ → PontryaginDual C𝔽}
    (hχ : IsSpectralBasepointChoice χ) (ψ : PontryaginDual C𝔽) :
    ∃ (ω : PontryaginDual C₁) (τ : ℝ), ∀ σ t : ℝ, 0 < σ →
      meromorphicOrderAt (continuedCompletedHeckeL ψ) (shift(σ, t)) =
        meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) (shift(σ, (t + τ : ℝ))) :=
  ⟨_, order_eq_basepoint' hχ ψ⟩
end Charts

local notation "ord(" χ ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat

/-- The literal finite-lines hypothesis from #7453 on one S₃ field bounds the
union, over every rational Hecke character, of the real parts of the positive
divisor of the twisted cubic-to-rational L-function quotient. -/
theorem all_norm_twist_quotient_lines_finite
    (L k K : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    [Field k] [NumberField k] [Field K] [NumberField K]
    (hG : Nonempty ((L ≃ₐ[ℚ] L) ≃* Equiv.Perm (Fin 3)))
    (ιk : Nonempty (k →ₐ[ℚ] L)) (hkdeg : Module.finrank ℚ k = 2)
    (ιK : Nonempty (K →ₐ[ℚ] L)) (hKdeg : Module.finrank ℚ K = 3)
    (χ : PontryaginDual (ideleClassNorm L).ker → U[L]) (hχ : IsSpectralBasepointChoice χ)
    (hfin : {σ : ℝ | ∃ (ω : PontryaginDual (ideleClassNorm L).ker) (t : ℝ),
      1 < ord(χ ω, (σ : ℂ) + (t : ℂ) * Complex.I)}.Finite) :
    {σ : ℝ | ∃ (ψ : U[ℚ]) (z : ℂ), z.re = σ ∧ 0 < σ ∧ σ < 1 ∧
      ord(ψ, z) < ord(normPullback K ψ, z)}.Finite := by
  apply hfin.subset
  rintro σ ⟨ψ,z,rfl,h₀,h₁,hlt⟩
  have ho := norm_twist_order_relation L k K hG ιk hkdeg ιK hKdeg ψ h₀
  rw [strip_order (normPullback L ψ) z h₀ h₁, strip_order ψ z h₀ h₁,
    strip_order (normPullback k ψ) z h₀ h₁, strip_order (normPullback K ψ) z h₀ h₁] at ho
  have he := congrArg WithTop.untop₀ ho
  change (ord(normPullback L ψ, z) : ℤ) + 2 * ord(ψ, z) =
    (ord(normPullback k ψ, z) : ℤ) + 2 * ord(normPullback K ψ, z) at he
  have hmul : 1 < ord(normPullback L ψ, z) := by omega
  obtain ⟨ω,τ,hτ⟩ := order_eq_basepoint hχ (normPullback L ψ)
  refine ⟨ω,z.im + τ,?_⟩
  have hs := hτ z.re z.im h₀
  rw [Complex.re_add_im] at hs
  simpa only [← hs] using hmul

/-- The complementary global order bound #7220 on the closure gives half as
large a bound for each positive quotient multiplicity, simultaneously over the
full rational unitary dual. -/
theorem all_norm_twist_quotient_half_bound
    (L k K : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    [Field k] [NumberField k] [Field K] [NumberField K]
    (hG : Nonempty ((L ≃ₐ[ℚ] L) ≃* Equiv.Perm (Fin 3)))
    (ιk : Nonempty (k →ₐ[ℚ] L)) (hkdeg : Module.finrank ℚ k = 2)
    (ιK : Nonempty (K →ₐ[ℚ] L)) (hKdeg : Module.finrank ℚ K = 3)
    (χ : PontryaginDual (ideleClassNorm L).ker → U[L]) (hχ : IsSpectralBasepointChoice χ)
    (M : ℕ) (hM : ∀ (ω : PontryaginDual (ideleClassNorm L).ker) (σ t : ℝ),
      ord(χ ω, (σ : ℂ) + (t : ℂ) * Complex.I) ≤ M)
    (ψ : U[ℚ]) (z : ℂ) (h₀ : 0 < z.re) (h₁ : z.re < 1) :
    ord(normPullback K ψ, z) - ord(ψ, z) ≤ M / 2 := by
  have ho := norm_twist_order_relation L k K hG ιk hkdeg ιK hKdeg ψ h₀
  rw [strip_order (normPullback L ψ) z h₀ h₁, strip_order ψ z h₀ h₁,
    strip_order (normPullback k ψ) z h₀ h₁, strip_order (normPullback K ψ) z h₀ h₁] at ho
  have he := congrArg WithTop.untop₀ ho
  change (ord(normPullback L ψ, z) : ℤ) + 2 * ord(ψ, z) =
    (ord(normPullback k ψ, z) : ℤ) + 2 * ord(normPullback K ψ, z) at he
  obtain ⟨ω,τ,hτ⟩ := order_eq_basepoint hχ (normPullback L ψ)
  have hs := hτ z.re z.im h₀
  rw [Complex.re_add_im] at hs
  have hb := hM ω z.re (z.im + τ)
  rw [← hs] at hb
  omega
/-- The finite rational character attached to a primitive Dirichlet character,
chosen together with its equality on all ideles and its finite L-series. -/
private def rationalLift {N : ℕ} [NeZero N] {ξ : DirichletCharacter ℂ N} (hξ : ξ.IsPrimitive) :
    U[ℚ] := (DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hξ).choose

def twistedQuotient {K : Type} [Field K] [NumberField K]
    {N : ℕ} [NeZero N] {ξ : DirichletCharacter ℂ N} (hξ : ξ.IsPrimitive) : ℂ → ℂ :=
  continuation (normPullback K (rationalLift hξ)) / DirichletCharacter.LFunction ξ

abbrev cubicPoly : Polynomial ℚ := Polynomial.X ^ 3 - Polynomial.C 2

private theorem cubicIrreducible : Irreducible cubicPoly := by
  apply irreducible_X_pow_sub_C_of_prime (by decide : Nat.Prime 3)
  intro q hq
  have h := congrArg (padicValRat 2) hq
  rw [padicValRat.pow, show padicValRat 2 2 = 1 from padicValRat.self (by decide : 1 < 2)] at h
  norm_num at h
  omega

local instance : Fact (Irreducible cubicPoly) := ⟨cubicIrreducible⟩
abbrev cubicField := AdjoinRoot cubicPoly
abbrev cubicClosure := cubicPoly.SplittingField
local instance : NumberField cubicClosure := ⟨⟩

/-- One set of lines, independent of both conductor and height, for every
positive order of the finite L-function quotient of the cubic Dirichlet twist
by its rational Dirichlet L-function. The hypothesis is exactly the unproved
finite-lines assertion #7453, used on one explicit number field. -/
theorem primitive_dirichlet_twisted_cubic_lines
    (χ : PontryaginDual (ideleClassNorm cubicClosure).ker → U[cubicClosure])
    (hχ : IsSpectralBasepointChoice χ)
    (hfin : {σ : ℝ | ∃ (ω : PontryaginDual (ideleClassNorm cubicClosure).ker) (t : ℝ),
      1 < ord(χ ω, (σ : ℂ) + (t : ℂ) * Complex.I)}.Finite) :
    {σ : ℝ | ∃ (N : ℕ) (_ : NeZero N) (ξ : DirichletCharacter ℂ N) (hξ : ξ.IsPrimitive)
      (z : ℂ), z.re = σ ∧ 0 < σ ∧ σ < 1 ∧ 0 < meromorphicOrderAt (twistedQuotient (K := cubicField) hξ) z}.Finite := by
  let k := (Polynomial.X ^ 2 + Polynomial.C (3 : ℚ)).SplittingField
  have : NumberField k := ⟨⟩
  have : IsGalois ℚ cubicClosure := IsGalois.of_separable_splitting_field cubicIrreducible.separable
  let b := AdjoinRoot.powerBasis (Polynomial.X_pow_sub_C_ne_zero (by decide : 0 < 3) (2 : ℚ))
  have hd : b.dim = 3 := by rw [AdjoinRoot.powerBasis_dim, Polynomial.natDegree_X_pow_sub_C]
  obtain ⟨ιK, ιk, hk⟩ := spectralLineJet_memLp_false_subfields cubicPoly rfl cubicIrreducible
  have G := spectralLineJet_memLp_false_cubicGalois cubicPoly rfl cubicIrreducible
  apply (all_norm_twist_quotient_lines_finite cubicClosure k cubicField G ιk hk ιK
    (b.finrank.trans hd) χ hχ hfin).subset
  rintro σ ⟨N,hN,ξ,hξ,z,rfl,h₀,h₁,hz⟩
  let ψ := rationalLift hξ
  let θ := normPullback cubicField ψ
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
  refine ⟨ψ,z,rfl,h₀,h₁,?_⟩
  change ord(ψ, z) < ord(θ, z)
  omega

/-- The right-hand zero-free width is independent of conductor and height. The
positive divisor tests the quotient after removal of common zeros. -/
theorem primitive_dirichlet_twisted_cubic_right_margin
    (χ : PontryaginDual (ideleClassNorm cubicClosure).ker → U[cubicClosure])
    (hχ : IsSpectralBasepointChoice χ)
    (hfin : {σ : ℝ | ∃ (ω : PontryaginDual (ideleClassNorm cubicClosure).ker) (t : ℝ),
      1 < ord(χ ω, (σ : ℂ) + (t : ℂ) * Complex.I)}.Finite) :
    ∃ δ > (0 : ℝ), δ ≤ 1 ∧ ∀ (N : ℕ) (_ : NeZero N)
      (ξ : DirichletCharacter ℂ N) (hξ : ξ.IsPrimitive) (z : ℂ),
      1 - δ < z.re → z.re < 1 → meromorphicOrderAt (twistedQuotient (K := cubicField) hξ) z ≤ 0 := by
  let S := {σ : ℝ | ∃ (N : ℕ) (_ : NeZero N) (ξ : DirichletCharacter ℂ N) (hξ : ξ.IsPrimitive)
    (z : ℂ), z.re = σ ∧ 0 < σ ∧ σ < 1 ∧ 0 < meromorphicOrderAt (twistedQuotient (K := cubicField) hξ) z}
  have hf : S.Finite := primitive_dirichlet_twisted_cubic_lines χ hχ hfin
  obtain ⟨m,hm,hmax⟩ := Set.exists_max_image (insert 0 S) id (hf.insert 0) (insert_nonempty _ _)
  have hm₀ : (0 : ℝ) ≤ m := hmax 0 (mem_insert _ _)
  have hm₁ : m < 1 := by
    rcases hm with rfl | h
    · exact zero_lt_one
    · obtain ⟨N,_,ξ,hξ,z,he,h₀,h₁,_⟩ := h
      exact h₁
  refine ⟨1-m, by linarith, by linarith, fun N _ ξ hξ z hz h₁ ↦ ?_⟩
  by_contra! hp
  have hS : z.re ∈ S := ⟨N,inferInstance,ξ,hξ,z,rfl,by linarith,h₁,hp⟩
  have he : z.re ≤ m := hmax _ (mem_insert_of_mem _ hS)
  linarith

open RiemannMasullo
open Lean Elab Command

private def auditRoot (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains n do throwError "unknown audit root {n}"
  let axioms ← Lean.collectAxioms n
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
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
  if !directSorry.isEmpty then throwError "{n} reaches admissions at {directSorry}"
  logInfo m!"{n}: {visited.size} reached declarations across {mods.size} modules; direct admissions: {directSorry}; kernel axioms {axioms}"

run_cmd auditRoot ``classNorm
run_cmd auditRoot ``norm_local
run_cmd auditRoot ``norm_twist_order_relation
run_cmd auditRoot ``all_norm_twist_quotient_lines_finite
run_cmd auditRoot ``all_norm_twist_quotient_half_bound
run_cmd auditRoot ``primitive_dirichlet_twisted_cubic_lines
run_cmd auditRoot ``primitive_dirichlet_twisted_cubic_right_margin

end TwistedCubic
end RiemannMasullo
