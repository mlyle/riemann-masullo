module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2

import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6
import RiemannMasullo.Ch03_IdelicZeta.Sec4
import RiemannMasullo.Ch02_AdelicTheta.Sec3
import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
import RiemannMasullo.Ch06_LocalGlobal.Sec3

import RiemannMasullo.AppC_LCTVS.Sec1
import all RiemannMasullo.Ch03_IdelicZeta.Sec3
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec1

/-! # §7.3.1 Orbital Schauder bases

The set of places in the Lean notation lists the finite places. All archimedean places
are included in the definition of the S-adeles.
-/

@[expose] public noncomputable section

open Asymptotics Filter Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "J₁" => (mₛ).ker
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "dualₛ" => dualQuasiCharacter (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chart(" χ ")" => twistₛ ((circleToComplex).comp (χ))
local notation "onComponent(" c ", " ω ")" =>
  (normOneRestriction mₛ c = (circleToComplex).comp ω)
local notation "Θₛ(" ω ")" => SLocalHomogeneousThetaSpace F S ω
local notation "Kₛ(" ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)
local notation "PV(" places ", " hT ", " ω ")" =>
  (sLocalHomogeneousThetaPrincipalValue (F := F) (S := S) (T := places) hT ω).range
local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))

/-- Paper: Situation 7.3.1.1(1), p. 340.
A finite set of places is saturated if it contains the entire fiber over every
rational prime that occurs below a member. -/
def IsSaturatedPlaceSet (S : Finset V) : Prop :=
  ∀ ⦃v w : V⦄, v ∈ S → w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S

/-- Paper: Situation 7.3.1.1(1), p. 340.
The empty set of finite places is saturated. -/
theorem isSaturatedPlaceSet_empty : IsSaturatedPlaceSet (∅ : Finset V) := by
  intro v w hv _
  exact absurd hv (Finset.notMem_empty v)

open Classical in
/-- Paper: Situation 7.3.1.1(2), p. 340.
The primary part of S at p consists of its places lying over p.
Deviation: A rational prime is represented by its place in the ring of integers of ℚ. -/
def sLocalPrimaryPlaces (S : Finset V) (p : Vℚ) : Finset V :=
  S.filter fun v ↦ v.under (𝓞 ℚ) = p

/-- Paper: Situation 7.3.1.1(2), p. 340.
A place belongs to the primary part exactly when it belongs to S and lies over p. -/
theorem mem_sLocalPrimaryPlaces (p : Vℚ) (v : V) :
    v ∈ sLocalPrimaryPlaces S p ↔ v ∈ S ∧ v.under (𝓞 ℚ) = p := by
  simp [sLocalPrimaryPlaces]

/-- Paper: Situation 7.3.1.1(2), p. 340.
The primary part is a subset of the selected finite places. -/
theorem sLocalPrimaryPlaces_subset (S : Finset V) (p : Vℚ) :
    sLocalPrimaryPlaces S p ⊆ S := by
  intro v hv
  exact ((mem_sLocalPrimaryPlaces p v).1 hv).1

/-- Paper: Situation 7.3.1.1(1)–(2), p. 340.
If S is saturated and its primary part at p is nonempty, that part contains every place over p. -/
theorem mem_sLocalPrimaryPlaces_of_saturated (p : Vℚ) (_hS : IsSaturatedPlaceSet S)
    (_hp : (sLocalPrimaryPlaces S p).Nonempty) (v : V) :
    v ∈ sLocalPrimaryPlaces S p ↔ v.under (𝓞 ℚ) = p := by
  rw [mem_sLocalPrimaryPlaces]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  obtain ⟨w, hw⟩ := _hp
  rw [mem_sLocalPrimaryPlaces] at hw
  exact _hS hw.1 (h.trans hw.2.symm)

-- The unitary lifts in Situation 7.3.1.1(3) use the norm-twist chart of §3.3 and §5.4.
-- TODO(paper-gap): Theorem 7.3.1.2 specifies that S₀ contains the archimedean places,
-- but the principal-value operator of §5.3 and the introduction on p. 340 use finite places.
-- Its proof also replaces m_S - m_{S₀} by m_{S₀} in the coefficient cutoff.

/-- Paper: Theorem 7.3.1.2, p. 341.
The indices consist of a center on the chosen component and a zero-based offset among the
highest coefficients removed by the selected finite principal values.
Deviation: The offset r selects the printed coefficient of pole order m_S(c) - r. -/
def SLocalOrbitalIndex (T : Finset V) (ω : PontryaginDual J₁) :=
  {j : Xₛ × ℕ // onComponent(j.1, ω) ∧ j.2 < sLocalFinitePoleMultiplicity T j.1}

local notation "I(" T ", " ω ")" => SLocalOrbitalIndex (F := F) (S := S) T ω

/-- Paper: Theorem 7.3.1.2, p. 341.
At the trivial character the admissible offsets are precisely those below the number
of selected finite places. -/
theorem sLocalOrbitalIndex_one_iff {T : Finset V} (_hT : T ⊆ S) (r : ℕ) :
    (∃ j : I(T, (1 : PontryaginDual J₁)), j.val = (1, r)) ↔ r < T.card := by
  have h1 : onComponent((1 : Xₛ), (1 : PontryaginDual J₁)) := by
    ext x
    simp [normOneRestriction]
    exact (map_one Circle.coeHom).symm
  have hm := sLocalFinitePoleMultiplicity_one (F := F) (S := S) T _hT
  constructor
  · rintro ⟨j, hj⟩
    have := j.property.2
    rw [hj] at this
    simpa [hm] using this
  · intro h
    exact ⟨⟨(1, r), h1, by simpa [hm] using h⟩, rfl⟩

/-- Paper: Theorem 7.3.1.2, p. 341.
The indexed functional is the selected Laurent coefficient on homogeneous theta classes. -/
def sLocalOrbitalPrincipalPart {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) : StrongDual ℂ (Θₛ(ω)) :=
  sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1
    (sLocalRhoPoleOrder j.val.1 - j.val.2)

/-- Paper: Theorem 7.3.1.2, p. 341.
Offset zero gives the coefficient of the highest allowed pole order on a test. -/
theorem sLocalOrbitalPrincipalPart_mk_top {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) (_hj : j.val.2 = 0) (f : ℬₛ) :
    sLocalOrbitalPrincipalPart j ((Kₛ(ω)).mkQL f) =
      sLocalZLaurentCoeff f j.val.1 (-(sLocalRhoPoleOrder j.val.1 : ℤ)) := by
  unfold sLocalOrbitalPrincipalPart
  rw [sLocalThetaPrincipalPartCoeff_mk]
  simp [_hj]

private theorem sLocalOrbitalPrincipalPart_range_le_ker_chart (c : Xₛ) :
    ∃ (χ : PontryaginDual Jₛ) (s : ℂ), ∀ z : ℂ, twistₛ c z = chart(χ) (s + z) := by
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  have hp := isProperMap_sIdeleQuotientNorm F S
  have hne : ∃ g, mₛ g ≠ 1 := by
    obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨τ t, (hτ t).trans_ne ht⟩
  let a := quasiCharacterAbscissa mₛ hp hne c
  let d := twistₛ c (-(a : ℂ))
  have hrad (g : Jₛ) : (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (a : ℂ) = (‖c g‖ : ℂ) := by
    rw [← Complex.ofReal_cpow (NNReal.coe_nonneg _) a,
      norm_quasiCharacter_eq_rpow_abscissa mₛ hp hne]
  have hd (g : Jₛ) : d g = c g / (‖c g‖ : ℂ) := by
    change c g * _ ^ (-(a : ℂ)) = _
    rw [Complex.cpow_neg, hrad, div_eq_mul_inv]
  have hn (g : Jₛ) : ‖c g‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit g).map c).ne_zero
  let χ : PontryaginDual Jₛ :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (by
        rw [hd, norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (hn g)])⟩
      map_one' := Subtype.ext d.map_one
      map_mul' x y := Subtype.ext (d.map_mul x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨χ, (a : ℂ), fun z ↦ ContinuousMonoidHom.ext fun g ↦ ?_⟩
  have hN : (((mₛ g : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ g).ne_zero)
  change c g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ z =
    d g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ ((a : ℂ) + z)
  rw [hd, Complex.cpow_add _ _ hN, hrad, ← mul_assoc, div_mul_cancel₀ _
    (Complex.ofReal_ne_zero.mpr (hn g))]

private theorem sLocalOrbitalPrincipalPart_range_le_ker_restrict (v : S) (c : Xₛ) (z : ℂ)
    (x : (v.val.adicCompletion F)ˣ) :
    sLocalFiniteRestriction v (twistₛ c z) x =
      sLocalFiniteRestriction v c x * (((‖(x : v.val.adicCompletion F)‖ : ℝ) : ℂ)) ^ z := by
  have h := sLocalFiniteRestriction_norm (F := F) (S := S) v x
  have e : ∀ (d : Xₛ) (w : ℂ), sLocalFiniteRestriction v (twistₛ d w) x =
      sLocalFiniteRestriction v d x * (sLocalFiniteRestriction v (chart(1) 1) x) ^ w := by
    intro d w
    obtain ⟨φ, hφ⟩ : ∃ φ : Jₛ, ∀ d : Xₛ, sLocalFiniteRestriction v d x = d φ :=
      ⟨_, fun d ↦ rfl⟩
    rw [hφ, hφ, hφ]
    change d φ * (((mₛ φ : ℝ≥0) : ℝ) : ℂ) ^ w = d φ * (((1 : PontryaginDual Jₛ) φ : Circle) *
      (((mₛ φ : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ)) ^ w
    rw [Complex.cpow_one, PontryaginDual.one_apply, Circle.coe_one, one_mul]
  rw [e]
  congr 2


private theorem sLocalOrbitalPrincipalPart_range_le_ker_euler (v : S) (c : Xₛ) :
    AnalyticAt ℂ (fun z ↦
      (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹) 0 := by
  classical
  let ι := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom
  have hunit (z : ℂ) (u : (v.val.adicCompletionIntegers F)ˣ) :
      sLocalFiniteRestriction v (twistₛ c z) (ι u) = sLocalFiniteRestriction v c (ι u) := by
    rw [sLocalOrbitalPrincipalPart_range_le_ker_restrict]
    have hu : ‖((ι u : (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F)‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
          (a := ι u)).mp ⟨u.val.property, u.inv.property⟩)
    rw [hu, Complex.ofReal_one, Complex.one_cpow, mul_one]
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : (v.val.adicCompletion F)ˣ, ∀ d : QuasiCharacter (v.val.adicCompletion F)ˣ,
      finiteLocalEulerFactor v.val d = if (∀ u, d (ι u) = 1) then (1 - d ϖ)⁻¹ else 1 :=
    ⟨_, fun d ↦ rfl⟩
  have key (z : ℂ) : (∀ u, sLocalFiniteRestriction v (twistₛ c z) (ι u) = 1) ↔
      (∀ u, sLocalFiniteRestriction v c (ι u) = 1) :=
    forall_congr' fun u ↦ by rw [hunit z u]
  by_cases hu : ∀ u, sLocalFiniteRestriction v c (ι u) = 1
  · have hfun : (fun z ↦ (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹) =
        fun z ↦ 1 - sLocalFiniteRestriction v c ϖ *
          (((‖(ϖ : v.val.adicCompletion F)‖ : ℝ) : ℂ)) ^ z := by
      funext z
      rw [hϖ, ite_cond_eq_true _ _ (eq_true ((key z).mpr hu)), inv_inv,
        sLocalOrbitalPrincipalPart_range_le_ker_restrict]
    rw [hfun]
    have hne : (((‖(ϖ : v.val.adicCompletion F)‖ : ℝ) : ℂ)) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, norm_ne_zero_iff]; exact ϖ.ne_zero
    simp_rw [Complex.cpow_def_of_ne_zero hne]
    fun_prop
  · have hfun : (fun z ↦ (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹) =
        fun _ ↦ 1 := by
      funext z
      rw [hϖ, ite_cond_eq_false _ _ (eq_false (fun h ↦ hu ((key z).mp h))), inv_one]
    rw [hfun]
    exact analyticAt_const

private theorem sLocalOrbitalPrincipalPart_range_le_ker_neg (o : WithTop ℤ) (h : o < 0) :
    1 ≤ -o := by
  induction o using WithTop.recTopCoe with
  | top => exact absurd h (by simp)
  | coe m =>
    have hm : m < 0 := by exact_mod_cast h
    have : ((-m : ℤ) : WithTop ℤ) = -(m : WithTop ℤ) := rfl
    rw [← this]
    exact_mod_cast (by omega : (1 : ℤ) ≤ -m)

open Classical in
private theorem sLocalOrbitalPrincipalPart_range_le_ker_prod (T : Finset V) (c : Xₛ) :
    MeromorphicAt (fun z : ℂ ↦ ∏ v : S, if v.val ∈ T then
        (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ else 1) 0 ∧
      ((sLocalFinitePoleMultiplicity T c : ℕ) : WithTop ℤ) ≤ meromorphicOrderAt
        (fun z : ℂ ↦ ∏ v : S, if v.val ∈ T then
          (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ else 1) 0 := by
  let E : S → ℂ → ℂ := fun v z ↦ finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z))
  let g : S → ℂ → ℂ := fun v z ↦ if v.val ∈ T then (E v z)⁻¹ else 1
  have hg (v : S) : AnalyticAt ℂ (g v) 0 := by
    by_cases hv : v.val ∈ T
    · simp only [g, hv, ite_true]; exact sLocalOrbitalPrincipalPart_range_le_ker_euler v c
    · simp only [g, hv, ite_false]; exact analyticAt_const
  have hQ : (fun z : ℂ ↦ ∏ v : S, if v.val ∈ T then
      (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ else 1) =
      ∏ v : S, g v := by
    funext z; simp only [Finset.prod_apply, g, E]
  rw [hQ]
  refine ⟨MeromorphicAt.prod fun v _ ↦ (hg v).meromorphicAt, ?_⟩
  rw [meromorphicOrderAt_prod fun v _ ↦ (hg v).meromorphicAt]
  unfold sLocalFinitePoleMultiplicity sLocalFinitePolePlaces
  rw [Finset.filter_filter, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_le_sum fun v _ ↦ ?_
  split_ifs with h
  · have hv : g v = (E v)⁻¹ := by funext z; simp only [g, h.2, ite_true, Pi.inv_apply]
    rw [hv, meromorphicOrderAt_inv, Nat.cast_one]
    exact sLocalOrbitalPrincipalPart_range_le_ker_neg _ h.1
  · rw [Nat.cast_zero]; exact (hg v).meromorphicOrderAt_nonneg


private theorem sLocalOrbitalPrincipalPart_range_le_ker_zeta (f : ℬₛ) (χ : PontryaginDual Jₛ)
    (s : ℂ) (c : Xₛ)
    (hc : ∀ z, twistₛ c z = chart(χ) (s + z)) :
    MeromorphicAt (fun z ↦ sLocalIdelicZFunction f (twistₛ c z)) 0 ∧
      ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (twistₛ c z)) 0 := by
  have hb := sLocalIdelicOrderBound_eq_neg_poleOrder (F := F) (S := S) c
  rw [← hb]
  unfold sLocalIdelicOrderBound
  simp only [hc]
  refine ⟨?_, ?_⟩
  · exact (((sLocalIdelicZFunction_meromorphic f χ).meromorphicOn (s + 0) trivial)).comp_analyticAt
      (g := fun t ↦ s + t) (by fun_prop)
  · have h := sLocalIdelicZFunction_poles f χ s
    have e1 := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (x := (0 : ℂ)) (c := s)
      (f := fun w ↦ sLocalRhoFactor (chart(χ) w))
    have e2 := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (x := (0 : ℂ)) (c := s)
      (f := fun w ↦ sLocalIdelicZFunction f (chart(χ) w))
    rw [zero_add] at e1 e2
    simp only [add_comm s]
    rw [e1, e2]
    exact h


open Classical in
private theorem sLocalOrbitalPrincipalPart_range_le_ker_polar {T : Finset V} (hT : T ⊆ S)
    (f : ℬₛ) (c : Xₛ) :
    sLocalPolarMultiplicity (sAdelePrincipalValue F hT f) c ≤
      sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c := by
  let g := sAdelePrincipalValue F hT f
  obtain ⟨χ, s, hc⟩ := sLocalOrbitalPrincipalPart_range_le_ker_chart c
  obtain ⟨hZm, hZo⟩ := sLocalOrbitalPrincipalPart_range_le_ker_zeta f χ s c hc
  obtain ⟨hQm, hQo⟩ := sLocalOrbitalPrincipalPart_range_le_ker_prod T c
  have ht : Tendsto (fun z : ℂ ↦ s + z) (𝓝[≠] 0) (𝓝[≠] s) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_const.add continuous_id : Continuous fun z : ℂ ↦ s + z).tendsto'
        (0 : ℂ) s (add_zero s)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact fun h ↦ hz (add_eq_left.mp h)
  have hev : (fun z ↦ sLocalIdelicZFunction g (twistₛ c z)) =ᶠ[𝓝[≠] 0]
      (fun z ↦ sLocalIdelicZFunction f (twistₛ c z)) * (fun z : ℂ ↦ ∏ v : S, if v.val ∈ T then
        (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ else 1) := by
    have h1 := nhdsNE_le_codiscrete s (sLocalIdelicZFunction_principalValue T hT f χ)
    filter_upwards [ht.eventually h1] with z hz
    try simp only at hz
    simp only [Pi.mul_apply, hc z]
    rw [hz, div_eq_mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    split_ifs <;> simp
  have hord : (((sLocalFinitePoleMultiplicity T c : ℤ) - sLocalRhoPoleOrder c : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction g (twistₛ c z)) 0 := by
    rw [meromorphicOrderAt_congr hev, meromorphicOrderAt_mul hZm hQm]
    have e2 : (((sLocalFinitePoleMultiplicity T c : ℤ) - sLocalRhoPoleOrder c : ℤ) : WithTop ℤ) =
        ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) +
          ((sLocalFinitePoleMultiplicity T c : ℕ) : WithTop ℤ) := by
      rw [show ((sLocalFinitePoleMultiplicity T c : ℕ) : WithTop ℤ) =
        (((sLocalFinitePoleMultiplicity T c : ℕ) : ℤ) : WithTop ℤ) from rfl, ← WithTop.coe_add]
      congr 1
      ring
    rw [e2]
    exact add_le_add hZo hQo
  unfold sLocalPolarMultiplicity
  generalize meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction g (twistₛ c z)) 0 = o at hord ⊢
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    have : (sLocalFinitePoleMultiplicity T c : ℤ) - sLocalRhoPoleOrder c ≤ n := by
      exact_mod_cast hord
    simp only [WithTop.untop₀_coe]
    omega

open Classical in
private theorem sLocalOrbitalPrincipalPart_range_le_ker_core {T : Finset V} (hT : T ⊆ S)
    (f : ℬₛ) (c : Xₛ) (r : ℕ)
    (hr' : r < sLocalFinitePoleMultiplicity T c) :
    sLocalZLaurentCoeff (sAdelePrincipalValue F hT f) c
      (-((sLocalRhoPoleOrder c - r : ℕ) : ℤ)) = 0 := by
  let g := sAdelePrincipalValue F hT f
  have hmult : sLocalFinitePoleMultiplicity T c ≤ sLocalRhoPoleOrder c := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces]
    unfold sLocalFinitePoleMultiplicity
    exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
  have hk : 0 < sLocalRhoPoleOrder c - r := by omega
  by_contra hne
  have hpole := (sLocalPrincipalPartCoeff_ne_zero_imp_pole c (sLocalRhoPoleOrder c - r) hk g
    (by rwa [sLocalPrincipalPartCoeff_apply])).2
  have hpm : sLocalPolarMultiplicity g c ≤
      sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c :=
    sLocalOrbitalPrincipalPart_range_le_ker_polar hT f c
  omega

private theorem sLocalOrbitalPrincipalPart_range_le_ker_range {M Q : Type*} [AddCommGroup M]
    [Module ℂ M] [AddCommGroup Q]
    [Module ℂ Q] [TopologicalSpace Q] (π : M →ₗ[ℂ] Q) (hπ : Function.Surjective π)
    (L : Q →ₗ[ℂ] Q) (φ : Q →L[ℂ] ℂ) (h : ∀ f, φ (L (π f)) = 0) :
    LinearMap.range L ≤ LinearMap.ker (φ : Q →ₗ[ℂ] ℂ) := by
  rintro x ⟨y, rfl⟩
  obtain ⟨f, rfl⟩ := hπ y
  exact h f

open Classical in
private theorem sLocalOrbitalPrincipalPart_range_le_ker_test {T : Finset V} (hT : T ⊆ S)
    (ω : PontryaginDual J₁) (j : I(T, ω)) (f : ℬₛ) :
    sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) j
      (sLocalHomogeneousThetaPrincipalValue hT ω ((Kₛ(ω)).mkQ f)) = 0 := by
  have e1 : sLocalHomogeneousThetaPrincipalValue hT ω ((Kₛ(ω)).mkQ f) =
      (Kₛ(ω)).mkQL (sAdelePrincipalValue F hT f) :=
    sLocalHomogeneousThetaPrincipalValue_mk hT ω f
  have e2 : sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) j
      ((Kₛ(ω)).mkQL (sAdelePrincipalValue F hT f)) =
      sLocalZLaurentCoeff (sAdelePrincipalValue F hT f) j.val.1
        (-((sLocalRhoPoleOrder j.val.1 - j.val.2 : ℕ) : ℤ)) :=
    sLocalThetaPrincipalPartCoeff_mk ω j.val.1 j.property.1 (sLocalRhoPoleOrder j.val.1 - j.val.2)
      (sAdelePrincipalValue F hT f)
  have e3 := sLocalOrbitalPrincipalPart_range_le_ker_core hT f j.val.1 j.val.2 j.property.2
  exact (congrArg _ e1).trans (e2.trans e3)

/-- Paper: Theorem 7.3.1.2(1), p. 341.
Every homogeneous theta class whose zeta transform obeys the remaining pole bound
on the component lies in the image of the finite principal value.
Deviation: The selected places are finite, as in Definition 5.3.1.4. This is the
reverse inclusion of `sLocalOrbitalPrincipalValue_eq_poleBound`. -/
theorem sLocalThetaPoleBound_le_orbitalPrincipalValue {T : Finset V} (hT : T ⊆ S)
    (_hne : T.Nonempty) (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial)
    (ω : PontryaginDual J₁) :
    sLocalThetaPoleBound ω (fun c ↦ sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c) ≤
      PV(T, hT, ω) := by
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨η, hη, _⟩ := exists_character_on_split mₛ
    (isProperMap_sIdeleQuotientNorm F S).continuous σ hσ ω 1
  obtain ⟨χ, hχ, hχrest, _⟩ := sLocal_character_extension η
  let C₁ := (ideleClassNorm F).ker
  let χ₀ := (circleToComplex).comp χ
  let ω𝔽 : PontryaginDual C₁ :=
    χ.comp (⟨C₁.subtype, continuous_subtype_val⟩ : C₁ →ₜ* _)
  have hχ₀ : ideleClassNormTwist χ 0 = χ₀ := by
    ext1 g
    change (χ g : ℂ) * _ ^ (0 : ℂ) = (χ g : ℂ)
    simp
  have hu : χ₀ ∈ unramifiedOutside F S := hχ₀ ▸ hχ
  have hbase : sIdeleRestriction F S ⟨χ₀, hu⟩ = (circleToComplex).comp η := by
    have hsub : (⟨χ₀, hu⟩ : unramifiedOutside F S) = ⟨ideleClassNormTwist χ 0, hχ⟩ :=
      Subtype.ext hχ₀.symm
    rw [hsub, hχrest]
    ext1 g
    change (η g : ℂ) * _ ^ (0 : ℂ) = (η g : ℂ)
    simp
  let hω : NormOneCharacterUnramifiedOutside ω𝔽 S := ⟨⟨χ₀, hu⟩, fun _ ↦ rfl⟩
  have hωlocal : sLocalNormOneCharacter S ω𝔽 hω = ω := by
    apply ContinuousMonoidHom.ext
    intro y
    apply Subtype.ext
    exact (sLocalNormOneCharacter_eq_sIdeleRestriction ω𝔽 ⟨χ₀, hu⟩ (fun _ ↦ rfl) y).trans
      ((DFunLike.congr_fun hbase y.val).trans (congrArg Subtype.val (hη y)))
  rintro x hx
  obtain ⟨f, rfl⟩ := (Kₛ(ω)).mkQ_surjective x
  have hbound := (mem_sLocalThetaPoleBound_iff ω _ ((Kₛ(ω)).mkQ f)).mp hx
  have hcoeff (c : Xₛ) (hc : onComponent(c, ω)) (hn : 0 < sLocalFinitePoleMultiplicity T c)
      (k : ℕ) (hk : sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c < k)
      (hkr : k ≤ sLocalRhoPoleOrder c) : sLocalPrincipalPartCoeff c k f = 0 := by
    rw [sLocalPrincipalPartCoeff_apply, ← sLocalThetaPrincipalPartCoeff_mk ω c hc k f]
    exact hbound c hc (by omega) k hk
  rw [← hωlocal] at hcoeff ⊢
  exact sLocalPrincipalValue_mem_range_of_coeff_eq_zero hT _hne _hPic χ hu f hcoeff

/-- The principal-value range lies in the pole-bound subspace: on the component, the
zeta transform of a principal value has the selected Euler poles removed. -/
private theorem sLocalOrbitalPrincipalValue_eq_poleBound_le {T : Finset V} (hT : T ⊆ S)
    (ω : PontryaginDual J₁) :
    PV(T, hT, ω) ≤ sLocalThetaPoleBound ω
      (fun c ↦ sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c) := by
  rintro x ⟨y, rfl⟩
  obtain ⟨f, rfl⟩ := (Kₛ(ω)).mkQ_surjective y
  exact Submodule.subset_span ⟨sAdelePrincipalValue F hT f,
    (sLocalHomogeneousThetaPrincipalValue_mk hT ω f).symm,
    fun c _ ↦ sLocalOrbitalPrincipalPart_range_le_ker_polar hT f c⟩

/-- Paper: Theorem 7.3.1.2(1), p. 341.
The principal-value range is the pole-bound subspace with the remaining multiplicity.
Deviation: The selected places are finite, as in Definition 5.3.1.4. -/
theorem sLocalOrbitalPrincipalValue_eq_poleBound {T : Finset V} (hT : T ⊆ S) (_hne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁) :
    PV(T, hT, ω) = sLocalThetaPoleBound ω
      (fun c ↦ sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c) := by
  exact le_antisymm (sLocalOrbitalPrincipalValue_eq_poleBound_le hT ω)
    (sLocalThetaPoleBound_le_orbitalPrincipalValue hT _hne _hS _hPic ω)

/-- Paper: Theorem 7.3.1.2(1), p. 341.
The principal-value image is the common kernel of the selected coefficients on the component.
Deviation: The selection is finite, as in the introduction and the principal-value operator
of §5.3. The cutoff is the one in the theorem statement. -/
theorem mem_sLocalOrbitalPrincipalValue_iff {T : Finset V} (h₀ : T ⊆ S) (_hne : T.Nonempty)
    (_hsat : IsSaturatedPlaceSet S) (_hclass : PicTrivial)
    (χ : PontryaginDual J₁) (x : Θₛ(χ)) :
    x ∈ PV(T, h₀, χ) ↔ ∀ j : I(T, χ),
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := χ) j x = 0 := by
  classical
  have hb := sLocalThetaRemovedPrincipalParts_ker (F := F) (S := S) χ ∅ T
  simp only [sLocalSelectedPoleMultiplicity_finite] at hb
  rw [sLocalOrbitalPrincipalValue_eq_poleBound h₀ _hne _hsat _hclass χ, ← hb,
    LinearMap.mem_ker]
  have hle (c : Xₛ) : sLocalFinitePoleMultiplicity T c ≤ sLocalRhoPoleOrder c := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces]
    unfold sLocalFinitePoleMultiplicity
    exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
  constructor
  · intro h j
    have hj := j.property.2
    have hm := hle j.val.1
    let k := sLocalRhoPoleOrder j.val.1 - j.val.2
    exact congrFun h ⟨(j.val.1, k), j.property.1, by
      rw [sLocalSelectedPoleMultiplicity_finite]; dsimp [k]; omega, Nat.sub_le _ _⟩
  · intro h
    funext i
    have hi := i.property.2.1
    rw [sLocalSelectedPoleMultiplicity_finite] at hi
    have hk := i.property.2.2
    let r := sLocalRhoPoleOrder i.val.1 - i.val.2
    have hr : r < sLocalFinitePoleMultiplicity T i.val.1 := by
      dsimp [r]; have := hle i.val.1; omega
    have hj := h ⟨(i.val.1, r), i.property.1, hr⟩
    change sLocalThetaPrincipalPartCoeff χ i.val.1 i.property.1
      (sLocalRhoPoleOrder i.val.1 - r) x = 0 at hj
    change sLocalThetaPrincipalPartCoeff χ i.val.1 i.property.1 i.val.2 x = 0
    rwa [show sLocalRhoPoleOrder i.val.1 - r = i.val.2 by dsimp [r]; omega] at hj

/-- Paper: Theorem 7.3.1.2(1), p. 341.
The finite principal-value image is closed in the homogeneous theta space.
Deviation: Uses the finite-place selection of part (1). -/
theorem sLocalOrbitalPrincipalValue_isClosed {T : Finset V} (hT : T ⊆ S) (_hTne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁) :
    IsClosed (PV(T, hT, ω) : Set (Θₛ(ω))) := by
  exact (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding (F := F) (S := S) hT ω).isClosed_range

/-- Paper: Theorem 7.3.1.2(2), p. 341.
Every continuous functional vanishing on the finite principal-value image lies in the
closed span of the selected coefficients in the strong dual.
Deviation: Uses the finite-place selection of part (1). This is the nontrivial inclusion
of `sLocalOrbitalPrincipalValue_annihilator`. -/
theorem sLocalOrbitalPrincipalValue_annihilator_le {T : Finset V} (hT : T ⊆ S)
    (_hTne : T.Nonempty) (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial)
    (ω : PontryaginDual J₁) :
    (PV(T, hT, ω)).dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) ≤
      (Submodule.span ℂ
        (range (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω)))).topologicalClosure := by
  let E := Θₛ(ω)
  have hN : IsNuclearTVS.{0} E := sLocalHomogeneousThetaSpace_nuclear (F := F) (S := S) ω
  let : T2Space E := hN.1
  let : PolynormableSpace ℂ E := hN.2.1
  let : MontelSpace ℂ E := (sLocalHomogeneousThetaSpace_montel (F := F) (S := S) ω).2
  apply le_of_eq
  apply strongDual_annihilator_eq_closedSpan_of_kernels
  intro x
  simpa only [Set.forall_mem_range] using
    (mem_sLocalOrbitalPrincipalValue_iff (F := F) hT _hTne _hS _hPic ω x)

/-- Each selected coefficient vanishes on the principal-value image. -/
private theorem sLocalOrbitalPrincipalValue_annihilator_ker {T : Finset V} (hT : T ⊆ S)
    (ω : PontryaginDual J₁) (i : I(T, ω)) :
    PV(T, hT, ω) ≤ (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) i).ker :=
  sLocalOrbitalPrincipalPart_range_le_ker_range ((Kₛ(ω)).mkQ) (Submodule.mkQ_surjective _)
    (sLocalHomogeneousThetaPrincipalValue hT ω)
    (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) i)
    (sLocalOrbitalPrincipalPart_range_le_ker_test hT ω i)

/-- The closed span of functionals vanishing on a submodule lies in its annihilator. -/
private theorem sLocalOrbitalPrincipalValue_annihilator_ge {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [ContinuousAdd (StrongDual ℂ E)] [ContinuousConstSMul ℂ (StrongDual ℂ E)]
    (R : Submodule ℂ E) (s : Set (StrongDual ℂ E)) (hs : ∀ φ ∈ s, ∀ x ∈ R, φ x = 0) :
    (Submodule.span ℂ s).topologicalClosure ≤
      R.dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) := by
  have hset : (R.dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) : Set (StrongDual ℂ E)) =
      ⋂ x ∈ R, {φ : StrongDual ℂ E | φ x = 0} := by
    ext φ
    simp only [SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
      Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  refine Submodule.topologicalClosure_minimal _ ?_ ?_
  · rw [Submodule.span_le, hset]
    intro φ hφ
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact hs φ hφ
  · rw [hset]
    exact isClosed_biInter fun x _ ↦ isClosed_eq (continuous_eval_const x) continuous_const

/-- Paper: Theorem 7.3.1.2(2), p. 341.
The annihilator of the finite principal-value image is the closed span of the selected
coefficients in the strong dual.
Deviation: Uses the finite-place selection of part (1). Lower Laurent coefficients can mix
under translations, as in §7.2. -/
theorem sLocalOrbitalPrincipalValue_annihilator {T : Finset V} (hT : T ⊆ S) (_hTne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁) :
    (PV(T, hT, ω)).dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) =
      (Submodule.span ℂ
        (range (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω)))).topologicalClosure := by
  refine le_antisymm (sLocalOrbitalPrincipalValue_annihilator_le hT _hTne _hS _hPic ω) ?_
  refine sLocalOrbitalPrincipalValue_annihilator_ge _ _ ?_
  rintro _ ⟨i, rfl⟩ x hx
  exact sLocalOrbitalPrincipalValue_annihilator_ker hT ω i hx

open Classical in
/-- Normalize a triangular witness and correct its later offsets at the same center. -/
private theorem sLocalOrbitalPrincipalPart_triangular_dual {E A C : Type*}
    [AddCommGroup E] [Module ℂ E] (center : A → C) (offset : A → ℕ)
    (cutoff : C → ℕ) (φ : A → E →ₗ[ℂ] ℂ)
    (hcut : ∀ i, offset i < cutoff (center i))
    (hinj : ∀ i j, center i = center j → offset i = offset j → i = j)
    (hwitness : ∀ j, ∃ x, φ j x ≠ 0 ∧
      ∀ i, center i ≠ center j ∨ offset i < offset j → φ i x = 0) :
    ∀ j, ∃ x, ∀ i, φ i x = if i = j then 1 else 0 := by
  classical
  let rank (i : A) := cutoff (center i) - offset i
  suffices h : ∀ n : ℕ, ∀ j, rank j = n → ∃ x, ∀ i, φ i x = if i = j then 1 else 0 by
    exact fun j ↦ h (rank j) j rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro j hj
    obtain ⟨x, hx, hzero⟩ := hwitness j
    let y := (φ j x)⁻¹ • x
    have hyj : φ j y = 1 := by simp [y, hx]
    let B := {i : A // center i = center j ∧ offset j < offset i}
    let index (i : B) : Fin (cutoff (center j)) :=
      ⟨offset i.val, by simpa only [i.property.1] using hcut i.val⟩
    let : Fintype B := Fintype.ofInjective index (fun i k h ↦ Subtype.ext
      (hinj i.val k.val (i.property.1.trans k.property.1.symm) (congrArg Fin.val h)))
    have hsmaller (i : B) : rank i.val < n := by
      have hlt := i.property.2
      have hc := hcut i.val
      rw [i.property.1] at hc
      rw [← hj]
      dsimp [rank]
      rw [i.property.1]
      omega
    choose z hz using fun i : B ↦ ih _ (hsmaller i) i.val rfl
    refine ⟨y - ∑ i : B, φ i.val y • z i, fun i ↦ ?_⟩
    simp only [map_sub, map_sum, map_smul, smul_eq_mul, hz, mul_ite, mul_one, mul_zero]
    have hsum : (∑ k : B, if i = k.val then φ k.val y else 0) =
        if center i = center j ∧ offset j < offset i then φ i y else 0 := by
      split_ifs with hi
      · let k : B := ⟨i, hi⟩
        rw [Finset.sum_eq_single k]
        · simp [k]
        · intro b _ hb
          exact ite_eq_right (fun h ↦ hb (Subtype.ext h.symm))
        · exact fun h ↦ (h (Finset.mem_univ k)).elim
      · apply Finset.sum_eq_zero
        intro k _
        apply ite_eq_right
        intro h
        exact hi (by simpa only [h] using k.property)
    rw [hsum]
    by_cases h : i = j
    · subst i
      simp [hyj]
    · rw [ite_eq_right h]
      by_cases hi : center i = center j ∧ offset j < offset i
      · simp [hi]
      · rw [ite_eq_right hi, sub_zero]
        have hz' : center i ≠ center j ∨ offset i < offset j := by
          by_cases hc : center i = center j
          · right
            have he : offset i ≠ offset j := fun h' ↦ h (hinj i j hc h')
            exact lt_of_le_of_ne (le_of_not_gt (fun h' ↦ hi ⟨hc, h'⟩)) he
          · exact Or.inl hc
        simp [y, hzero i hz']

section TriangularPrincipalPartTests

local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous

local notation "Z(" f ", " c ")" => (fun z ↦ sLocalIdelicZFunction f (twistₛ c z))

private theorem sLocalOrbital_centered_order (f : Xₛ → ℂ) (d : Xₛ) (a : ℂ) :
    meromorphicOrderAt (fun z ↦ f (twistₛ (twistₛ d a) z)) 0 =
      meromorphicOrderAt (fun z ↦ f (twistₛ d z)) a := by
  have he : (fun z ↦ f (twistₛ (twistₛ d a) z)) =
      (fun z ↦ f (twistₛ d z)) ∘ (· + a) :=
    funext fun z ↦ congrArg f (normTwist_normTwist mₛ hmₛ d a z)
  rw [he, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]

private theorem sLocalOrbital_eventually_regular (c : Xₛ) :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), 0 ≤ sLocalIdelicOrderBound (twistₛ c z) := by
  obtain ⟨χ, a, ha⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  have he : (fun z ↦ sLocalRhoFactor (twistₛ c z)) =
      (fun z ↦ sLocalRhoFactor (chart(χ) z)) ∘ (· + a) := by
    funext z
    rw [← ha]
    exact congrArg sLocalRhoFactor (normTwist_normTwist mₛ hmₛ _ a z)
  have hm : MeromorphicAt (fun z ↦ sLocalRhoFactor (twistₛ c z)) 0 := by
    rw [he]
    exact (sLocalRhoFactor_meromorphic χ (0 + a)).comp_analyticAt
      (g := fun z : ℂ ↦ z + a) (by fun_prop)
  filter_upwards [hm.eventually_analyticAt] with z hz
  change 0 ≤ min 0 (meromorphicOrderAt (fun w ↦ sLocalRhoFactor (twistₛ (twistₛ c z) w)) 0)
  rw [sLocalOrbital_centered_order]
  exact le_min le_rfl hz.meromorphicOrderAt_nonneg

/-- The product of the local standard Gaussians is normalized to a nonzero value at the given center. -/
private theorem exists_sLocalGaussian_normalized_ne_zero (c : Xₛ) :
    ∃ f : ℬₛ, sLocalNormalizedZFunction f c ≠ 0 := by
  classical
  obtain ⟨χ, a, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  let d := twistₛ ((circleToComplex).comp χ) a
  let i (w : InfinitePlace F) : w.Completionˣ →ₜ* Jₛ :=
    let h := sLocalInfiniteInsertion_properties (F := F) (S := S) w
    ⟨{ toFun := _, map_one' := h.1, map_mul' := h.2.1 }, h.2.2⟩
  let χArch (w : InfinitePlace F) := χ.comp (i w)
  have hχ (w : InfinitePlace F) :
      (circleToComplex).comp (χArch w) = sLocalInfiniteRestriction w ((circleToComplex).comp χ) := rfl
  let G (w : InfinitePlace F) := Multiplicative w.Completion
  let (w : InfinitePlace F) : T2Space (G w) := (inferInstance : T2Space w.Completion)
  let (w : InfinitePlace F) : LocallyCompactSpace (G w) := (inferInstance : LocallyCompactSpace w.Completion)
  let (w : InfinitePlace F) : SecondCountableTopology (G w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  obtain ⟨g, hg⟩ := schwartzBruhat_pi_test G (fun w ↦ infiniteStandardGaussian w (χArch w))
  let e : Multiplicative (InfiniteAdeleRing F) ≃ₜ* ((w : InfinitePlace F) → G w) :=
    { toFun := fun x w ↦ Multiplicative.ofAdd (x.toAdd w)
      invFun := fun x ↦ Multiplicative.ofAdd (fun w ↦ (x w).toAdd)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  let : T2Space (Multiplicative (InfiniteAdeleRing F)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing F)) :=
    e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let a₀ : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) :=
    ⟨g.val ∘ e, schwartzBruhat_mem_comp_equiv e g.property⟩
  let f := sLocalStandardThetaTensor d a₀
  have hf := sLocalNormalizedEigendistribution_gaussian χ a χArch hχ f
    (fun x ↦ (sLocalStandardThetaTensor_apply d a₀ x).trans (congrArg (· * _) (hg (e (Multiplicative.ofAdd x.1)))))
  have he := (existsUnique_sLocalNormalizedEigendistribution d).exists.choose_spec f
  change _ * sLocalNormalizedEigendistribution d f = sLocalNormalizedZFunction f d at he
  change sLocalNormalizedEigendistribution d f = 1 at hf
  refine ⟨f, ?_⟩
  change sLocalNormalizedZFunction f d ≠ 0
  rw [← he, hf, mul_one]
  apply Complex.ofReal_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_ne_zero]
  refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.mpr ?_⟩
  refine (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne'
  exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.val).trans' zero_lt_one


/-- A standard local test realizes the full Euler pole at a polar center. -/
private theorem exists_sLocalZeta_full_pole (c : Xₛ) (hc : 0 < sLocalRhoPoleOrder c) :
    ∃ f : ℬₛ, meromorphicOrderAt Z(f,c) 0 =
      ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨f, hf⟩ := exists_sLocalGaussian_normalized_ne_zero c
  refine ⟨f, ?_⟩
  obtain ⟨χ, a, ha⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  let L : ℂ → ℂ := fun z ↦ sLocalHeckeL (twistₛ c z)
  have hLbound : min 0 (meromorphicOrderAt L 0) =
      ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) := by
    have he : min 0 (meromorphicOrderAt L 0) = sLocalIdelicOrderBound c := by
      dsimp only [L]
      unfold sLocalIdelicOrderBound
      rw [← ha, sLocalOrbital_centered_order, sLocalOrbital_centered_order]
      exact sLocalHeckeL_poleOrder_eq (F := F) S χ a
    exact he.trans (sLocalIdelicOrderBound_eq_neg_poleOrder c)
  have hlt : min 0 (meromorphicOrderAt L 0) < 0 := by
    rw [hLbound]
    exact_mod_cast (show -(sLocalRhoPoleOrder c : ℤ) < 0 by omega)
  have hLo : meromorphicOrderAt L 0 = ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) :=
    (min_eq_right ((min_lt_iff.mp hlt).resolve_left (lt_irrefl _)).le).symm.trans hLbound
  let N := Z(f,c) / L
  change toMeromorphicNFOn N univ 0 ≠ 0 at hf
  have hN : MeromorphicOn N univ := by
    by_contra h
    exact hf (congrFun (toMeromorphicNFOn_of_not_meromorphicOn h) 0)
  have hNo : meromorphicOrderAt N 0 = 0 := by
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hN (mem_univ _)] at hf
    exact ((hN 0 trivial).meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero).mpr hf
  have hLm := meromorphicAt_of_meromorphicOrderAt_ne_zero
    (((min_lt_iff.mp hlt).resolve_left (lt_irrefl _)).ne)
  have hNZ : Z(f,c) =ᶠ[𝓝[≠] (0 : ℂ)] N * L := by
    filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero hLm).mp
      (hLo.trans_ne WithTop.coe_ne_top)] with z hz
    exact (div_mul_cancel₀ _ hz).symm
  rw [meromorphicOrderAt_congr hNZ, meromorphicOrderAt_mul (hN 0 trivial) hLm, hNo, zero_add, hLo]

section CompactNormAverage

open Bornology Function MeasureTheory

private theorem exists_intervalAverage {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [ContinuousSMul ℂ E]
    [LocallyConvexSpace ℝ E] [QuasiCompleteSpace ℂ E] (f : ℝ → E) (hf : Continuous f) :
    ∃ v : E, ∀ ℓ : StrongDual ℂ E, ℓ v = ∫ t in (0 : ℝ)..1, ℓ (f t) := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure μ := ⟨by
    change volume.restrict (Ioc (0 : ℝ) 1) univ < ⊤
    simp⟩
  have hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1 :=
    (ae_restrict_mem measurableSet_Ioc).mono fun _ hx ↦ Ioc_subset_Icc_self hx
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  have hi : PettisWeaklyIntegrable (.positive μ) f := by
    intro ℓ
    have h := ℓ.continuous.comp hf
    obtain ⟨r, hr⟩ := isCompact_Icc.exists_bound_of_continuousOn h.continuousOn
    exact (integrable_const (μ := μ) r).mono' h.aestronglyMeasurable (hμ.mono hr)
  let C := closure (convexHull ℝ (insert 0 (f '' Icc (0 : ℝ) 1)))
  have hc : IsCompact (insert 0 (f '' Icc (0 : ℝ) 1)) := (isCompact_Icc.image hf).insert 0
  have hC : IsCompact C :=
    isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := ℂ) hc.totallyBounded.convexHull
  obtain ⟨v, -, _, he⟩ := exists_hasPettisIntegral_mem_smul_of_isCompact_convex μ hi hC
    (convex_convexHull ..).closure (subset_closure (subset_convexHull _ _ (mem_insert _ _)))
    (hμ.mono fun x hx ↦ subset_closure (subset_convexHull _ _ (mem_insert_of_mem _ ⟨x, hx, rfl⟩)))
  refine ⟨v, fun ℓ ↦ ?_⟩
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact congrArg (fun z : PettisWeakCompletion E ↦
    (show Module.Dual ℂ (StrongDual ℂ E) from z) ℓ) he

private theorem exists_sLocalUnitOrbitAverage (u : ℝ → (SAdeleRing F S)ˣ) (hu : Continuous u)
    (w : ℝ → ℂ) (hw : Continuous w) (f : ℬₛ) :
    ∃ v : ℬₛ, ∀ ℓ : StrongDual ℂ ℬₛ,
      ℓ v = ∫ t in (0 : ℝ)..1, w t * ℓ (schwartzBruhatUnitTranslate (u t) f) := by
  let : T2Space ℬₛ := (sAdeleSchwartz_nuclear.{_,0} F S).1
  let : PolynormableSpace ℂ ℬₛ := (sAdeleSchwartz_nuclear.{_,0} F S).2.1
  let : LocallyConvexSpace ℝ ℬₛ := (PolynormableSpace.withSeminorms ℂ ℬₛ).toLocallyConvexSpace
  let : CompleteSpace ℬₛ := sAdeleSchwartz_complete F S
  have h : Continuous fun t ↦ schwartzBruhatUnitTranslate (u t) f :=
    continuous_sAdeleSchwartz_unitTranslate.comp (hu.prodMk continuous_const)
  obtain ⟨v, hv⟩ := exists_intervalAverage _ (hw.smul h)
  exact ⟨v, fun ℓ ↦ by simpa only [Pi.smul_apply', map_smul, smul_eq_mul, RingHom.id_apply] using hv ℓ⟩

private theorem exists_sLocalLogNormSection :
    ∃ u : ℝ → (SAdeleRing F S)ˣ, Continuous u ∧ ∀ t, ((sIdeleNorm F S (u t)).val : ℝ) = Real.exp t := by
  let σ := (Units.map (adeleProjection F S).toMonoidHom).comp (canonicalIdeleNormSection F)
  let r (t : ℝ) := (Nonneg.unitsHomeomorphPos ℝ).symm (Real.expOrderIso t)
  have hr : Continuous r := (Nonneg.unitsHomeomorphPos ℝ).symm.continuous.comp Real.expOrderIso.continuous
  have hp : Continuous (Units.map (adeleProjection F S).toMonoidHom) :=
    (continuous_fst.prodMk (continuous_pi fun v : S ↦
      (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  refine ⟨fun t ↦ σ (r t), hp.comp ((canonicalIdeleNormSection_continuous F).comp hr), ?_⟩
  intro t
  rw [show sIdeleNorm F S (σ (r t)) = r t from sIdeleNorm_project_canonicalSection F S _]
  rfl

private theorem intervalAverage_exp_neg (c : ℂ) (hc : c ≠ 0) :
    (∫ t in (0 : ℝ)..1, Complex.exp (-c * t)) = (1 - Complex.exp (-c)) / c := by
  rw [integral_exp_mul_complex (neg_ne_zero.mpr hc)]
  simp
  ring

private theorem exists_sLocalRegularEval (c : Xₛ) (hc : 0 ≤ sLocalIdelicOrderBound c) :
    ∃ ℓ : StrongDual ℂ ℬₛ, ∀ f, ℓ f = sLocalIdelicZFunction f c := by
  let d : {c : Xₛ // 0 ≤ sLocalIdelicOrderBound c} := ⟨c, hc⟩
  let M := (Submodule.subtype _).comp (sLocalIdelicMellin (F := F) (S := S))
  let ℓ : ℬₛ →ₗ[ℂ] ℂ := (ContinuousMap.evalCLM ℂ d).toLinearMap.comp M
  refine ⟨⟨ℓ, ?_⟩, fun _ ↦ rfl⟩
  exact (ContinuousMap.evalCLM ℂ d).continuous.comp sLocalIdelicMellin_continuous.subtype_val

private theorem sLocalLogSection_twist (c₀ : Xₛ) (g : (SAdeleRing F S)ˣ) (z : ℂ) (r : ℝ)
    (hr : ((sIdeleNorm F S g).val : ℝ) = Real.exp r) :
    (twistₛ c₀ z) (QuotientGroup.mk g) =
      c₀ (QuotientGroup.mk g) * Complex.exp ((r : ℂ) * z) := by
  change c₀ _ * (((((sIdeleNorm F S g).val : ℝ) : ℂ)) ^ z) = _
  rw [hr, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]

private theorem sLocalRegularEval_translate (c : Xₛ) (hc : 0 ≤ sLocalIdelicOrderBound c)
    (u : (SAdeleRing F S)ˣ) (f : ℬₛ) (ℓ : StrongDual ℂ ℬₛ)
    (hℓ : ∀ f, ℓ f = sLocalIdelicZFunction f c) :
    ℓ (schwartzBruhatUnitTranslate u f) = c (QuotientGroup.mk u) * ℓ f := by
  rw [hℓ, hℓ]
  exact sLocalIdelicMellin_unitTranslate (F := F) (S := S) u f ⟨c, hc⟩

private theorem exists_sLocalMellin_dividedFactor (c₀ : Xₛ) {L : ℝ} (hL : L ≠ 0) (f : ℬₛ) :
    ∃ v : ℬₛ, ∀ z : ℂ, z ≠ 0 → 0 ≤ sLocalIdelicOrderBound (twistₛ c₀ z) →
      sLocalIdelicZFunction v (twistₛ c₀ z) =
        (1 - Complex.exp (-(L : ℂ) * z)) / ((L : ℂ) * z) * sLocalIdelicZFunction f (twistₛ c₀ z) := by
  obtain ⟨u, hu, hN⟩ := exists_sLocalLogNormSection (F := F) (S := S)
  let γ (t : ℝ) := u (-L * t)
  let x (t : ℝ) : Jₛ := QuotientGroup.mk (γ t)
  have hγ : Continuous γ := hu.comp (continuous_const.mul continuous_id)
  have hx : Continuous x := QuotientGroup.continuous_mk.comp hγ
  have hc (t : ℝ) : c₀ (x t) ≠ 0 := ((Group.isUnit _).map c₀).ne_zero
  obtain ⟨v, hv⟩ := exists_sLocalUnitOrbitAverage (F := F) (S := S) γ hγ _ ((c₀.continuous.comp hx).inv₀ hc) f
  refine ⟨v, ?_⟩
  intro z hz hreg
  let d : Xₛ := twistₛ c₀ z
  change 0 ≤ sLocalIdelicOrderBound d at hreg
  change sLocalIdelicZFunction v d = _ * sLocalIdelicZFunction f d
  obtain ⟨ℓ, hℓ⟩ := exists_sLocalRegularEval (F := F) (S := S) d hreg
  have hval (t : ℝ) : (twistₛ c₀ z) (x t) = c₀ (x t) * Complex.exp (-((L : ℂ) * z) * t) := by
    rw [show (twistₛ c₀ z) (x t) = _ from sLocalLogSection_twist (F := F) (S := S)
      c₀ (γ t) z (-L * t) (hN _), Complex.ofReal_mul, Complex.ofReal_neg]
    congr 2
    ring
  rw [← hℓ v, hv ℓ, ← hℓ f]
  calc
    _ = ∫ t in (0 : ℝ)..1, Complex.exp (-((L : ℂ) * z) * t) * ℓ f := by
      refine intervalIntegral.integral_congr fun t _ ↦ ?_
      change (c₀ (x t))⁻¹ * ℓ (schwartzBruhatUnitTranslate (γ t) f) = _
      rw [sLocalRegularEval_translate (F := F) (S := S) d hreg (γ t) f ℓ hℓ]
      change (c₀ (x t))⁻¹ * ((twistₛ c₀ z) (x t) * ℓ f) = _
      rw [hval, ← mul_assoc, inv_mul_cancel_left₀ (hc t)]
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, intervalAverage_exp_neg _ (mul_ne_zero
        (Complex.ofReal_ne_zero.mpr hL) hz), neg_mul]

/-- Averaging a local Schwartz test over a compact interval of norm translations
multiplies its centered Mellin germ by the divided exponential factor. -/
private theorem exists_sLocalMellin_dividedFactor_germ (c₀ : Xₛ) {L : ℝ} (hL : L ≠ 0) (f : ℬₛ) :
    ∃ v : ℬₛ, ∀ (c : Xₛ) (b : ℂ), twistₛ c₀ b = c →
      (fun z ↦ sLocalIdelicZFunction v (twistₛ c z)) =ᶠ[𝓝[≠] (0 : ℂ)]
        fun z ↦ ((1 - Complex.exp (-(L : ℂ) * (z + b))) / ((L : ℂ) * (z + b))) *
          sLocalIdelicZFunction f (twistₛ c z) := by
  obtain ⟨v, hv⟩ := exists_sLocalMellin_dividedFactor (F := F) (S := S) c₀ hL f
  refine ⟨v, ?_⟩
  intro c b hcb
  have hreg := sLocalOrbital_eventually_regular c
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] 0, z ≠ 0 := self_mem_nhdsWithin (a := (0 : ℂ)) (s := {0}ᶜ)
  have hn : ∀ᶠ z : ℂ in 𝓝[≠] 0, z + b ≠ 0 := by
    by_cases hb : b = 0
    · simpa only [hb, add_zero] using hne
    · filter_upwards [eventually_ne_nhdsWithin (s := {(0 : ℂ)}ᶜ) (show (0 : ℂ) ≠ -b by simpa using hb)] with z hz
      exact fun h ↦ hz (eq_neg_of_add_eq_zero_left h)
  filter_upwards [hreg, hn] with z h hz'
  have heq : twistₛ c z = twistₛ c₀ (z + b) := by
    rw [← hcb]
    have e := normTwist_normTwist (G := Jₛ) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous c₀ b z
    exact e
  exact heq.symm ▸ hv (z + b) hz' (heq ▸ h)

end CompactNormAverage

/-- Residues only depend on the germ on a punctured neighbourhood. -/
private theorem orbitalResidue_congr {g h : ℂ → ℂ}
    (he : g =ᶠ[𝓝[≠] (0 : ℂ)] h) : complexResidue g 0 = complexResidue h 0 := by
  obtain ⟨δ, hδ, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he
  unfold complexResidue limUnder
  refine congrArg lim (Filter.map_congr ?_)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  rw [circleIntegral.integral_congr hr.1.le fun z hz ↦ hEq ⟨?_, ?_⟩]
  · rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
    exact hr.2
  · rintro rfl
    exact hr.1.ne (by simpa using hz)

/-- An exact pole order gives a nonzero coefficient at that order. -/
private theorem sLocalPrincipalPartCoeff_ne_zero_of_centered_order (f : ℬₛ) (c : Xₛ) (k : ℕ)
    (h : meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (twistₛ c z)) 0 = ((-(k : ℤ) : ℤ) : WithTop ℤ)) :
    sLocalPrincipalPartCoeff c k f ≠ 0 := by
  let Z : ℂ → ℂ := fun z ↦ sLocalIdelicZFunction f (twistₛ c z)
  obtain ⟨χ, s, hs⟩ := sLocalOrbitalPrincipalPart_range_le_ker_chart c
  have hmer : MeromorphicAt Z 0 := (sLocalOrbitalPrincipalPart_range_le_ker_zeta f χ s c hs).1
  obtain ⟨G, hG, hG0, hEq⟩ := (meromorphicOrderAt_eq_int_iff hmer).mp h
  rw [sLocalPrincipalPartCoeff_apply]
  change complexResidue (fun z ↦ Z z / z ^ (-(k : ℤ) + 1)) 0 ≠ 0
  have he : (fun z ↦ Z z / z ^ (-(k : ℤ) + 1)) =ᶠ[𝓝[≠] 0] (fun z ↦ G z / (z - 0)) := by
    filter_upwards [hEq, self_mem_nhdsWithin] with z hz hz0
    have hn : z ≠ 0 := hz0
    rw [hz, sub_zero, smul_eq_mul, zpow_add₀ hn, zpow_one]
    field_simp [zpow_ne_zero _ hn]
  rwa [orbitalResidue_congr he, complexResidue_div_sub hG]


private theorem orbitalCoeff_zero_of_centered_order (f : ℬₛ) (c : Xₛ) (k : ℕ)
    (hk : 0 < k) (h : ((-(k : ℤ) : ℤ) : WithTop ℤ) < meromorphicOrderAt Z(f,c) 0) :
    sLocalPrincipalPartCoeff c k f = 0 := by
  by_contra hne
  have hc := (sLocalPrincipalPartCoeff_ne_zero_imp_pole c k hk f hne).2
  unfold sLocalPolarMultiplicity at hc
  induction ho : meromorphicOrderAt Z(f,c) 0 using WithTop.recTopCoe with
  | top => simp only [ho, WithTop.untop₀_top, neg_zero, Int.toNat_zero] at hc; omega
  | coe n =>
    rw [ho, WithTop.coe_lt_coe] at h
    simp only [ho, WithTop.untop₀_coe] at hc
    omega

private theorem orbitalTriangularTest_of_centered_orders {T : Finset V} (ω : PontryaginDual J₁)
    (j : I(T,ω)) (f : ℬₛ)
    (hmain : meromorphicOrderAt Z(f,j.val.1) 0 =
      ((-(sLocalRhoPoleOrder j.val.1 - j.val.2 : ℕ) : ℤ) : WithTop ℤ))
    (hothers : ∀ i : I(T,ω), i.val.1 ≠ j.val.1 →
      (((sLocalFinitePoleMultiplicity T i.val.1 : ℤ) - sLocalRhoPoleOrder i.val.1 : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt Z(f,i.val.1) 0) :
    sLocalOrbitalPrincipalPart j ((Kₛ(ω)).mkQ f) ≠ 0 ∧
      ∀ i : I(T,ω), i.val.1 ≠ j.val.1 ∨ i.val.2 < j.val.2 →
        sLocalOrbitalPrincipalPart i ((Kₛ(ω)).mkQ f) = 0 := by
  classical
  have heval (i : I(T,ω)) :
      sLocalOrbitalPrincipalPart i ((Kₛ(ω)).mkQ f) =
        sLocalPrincipalPartCoeff i.val.1 (sLocalRhoPoleOrder i.val.1 - i.val.2) f :=
    sLocalThetaPrincipalPartCoeff_mk ω i.val.1 i.property.1 _ f
  rw [heval]
  refine ⟨sLocalPrincipalPartCoeff_ne_zero_of_centered_order f _ _ hmain, fun i hi ↦ ?_⟩
  rw [heval]
  have hr (i : I(T,ω)) : i.val.2 < sLocalRhoPoleOrder i.val.1 := by
    apply i.property.2.trans_le
    rw [sLocalRhoPoleOrder_eq_card_polePlaces]
    exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
  refine orbitalCoeff_zero_of_centered_order f _ _ (Nat.sub_pos_of_lt (hr i)) ?_
  by_cases hc : i.val.1 = j.val.1
  · have hlt := hi.resolve_left (not_not_intro hc)
    rw [hc, hmain, WithTop.coe_lt_coe]
    have hri := hr i
    have hrj := hr j
    rw [hc] at hri
    omega
  · apply lt_of_lt_of_le _ (hothers i hc)
    rw [WithTop.coe_lt_coe]
    have h := i.property.2
    have hri := hr i
    omega

private theorem orbitalEulerMultiplier_order {P E Z : ℂ → ℂ}
    (hE : AnalyticAt ℂ E 0) (hZ : MeromorphicAt Z 0) (b C : ℂ) (hC : C ≠ 0)
    (d : ℕ) (hEq : P =ᶠ[𝓝[≠] 0] fun z ↦ C * E z / (z + b) ^ d * Z z) :
    meromorphicOrderAt P 0 = meromorphicOrderAt E 0 -
      (if b = 0 then (d : WithTop ℤ) else 0) + meromorphicOrderAt Z 0 := by
  let D : ℂ → ℂ := fun z ↦ (z + b) ^ d
  have ha : AnalyticAt ℂ (fun z : ℂ ↦ z + b) 0 := analyticAt_id.add analyticAt_const
  have hD : AnalyticAt ℂ D 0 := ha.pow d
  have hden : meromorphicOrderAt D 0 = if b = 0 then (d : WithTop ℤ) else 0 := by
    by_cases hz : b = 0
    · simpa only [D, hz, add_zero, ite_true, sub_zero, Pi.pow_def] using (meromorphicOrderAt_pow_id_sub_const (x := (0 : ℂ)) (n := d))
    · rw [ite_eq_right hz, hD.meromorphicOrderAt_eq,
        hD.analyticOrderAt_eq_zero.mpr (by simpa [D] using pow_ne_zero d hz), ENat.map_zero]; rfl
  have hnum : AnalyticAt ℂ ((fun _ : ℂ ↦ C) * E) 0 := analyticAt_const.mul hE
  rw [meromorphicOrderAt_congr hEq]
  change meromorphicOrderAt (((fun _ : ℂ ↦ C) * E / D) * Z) 0 = _
  rw [meromorphicOrderAt_mul (hnum.meromorphicAt.div hD.meromorphicAt) hZ,
    meromorphicOrderAt_div hnum.meromorphicAt hD.meromorphicAt,
    meromorphicOrderAt_mul analyticAt_const.meromorphicAt hE.meromorphicAt,
    meromorphicOrderAt_const, ite_eq_right hC, zero_add, hden]

private theorem orbitalEulerMultiplier_center_order (n m r : ℕ) (hr : r < n) (hn : n ≤ m) :
    (n : WithTop ℤ) - ((n - r : ℕ) : WithTop ℤ) + ((-(m : ℤ) : ℤ) : WithTop ℤ) =
      ((-((m - r : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  change ((n : ℤ) : WithTop ℤ) - (((n - r : ℕ) : ℤ) : WithTop ℤ) +
    ((-(m : ℤ) : ℤ) : WithTop ℤ) = _
  rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_add, WithTop.coe_eq_coe]
  omega

private theorem orbitalEulerMultiplier_other_order (n m : ℕ) (o : WithTop ℤ)
    (h : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ o) :
    (((n : ℤ) - m : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ) + o := by
  change (((n : ℤ) - m : ℤ) : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ) + o
  rw [sub_eq_add_neg, WithTop.coe_add]
  exact add_le_add_right h _

/-- Reduces triangular interpolation to multiplication by the selected reciprocal
Euler product with the prescribed number of its center zeros divided out. -/
private theorem orbitalTriangularTest_of_euler_multiplier {T : Finset V} (ω : PontryaginDual J₁)
    (j : I(T,ω)) (base target : ℬₛ)
    (hbase : meromorphicOrderAt Z(base,j.val.1) 0 =
      ((-(sLocalRhoPoleOrder j.val.1 : ℤ) : ℤ) : WithTop ℤ))
    (e : I(T,ω) → ℂ → ℂ)
    (he : ∀ i, AnalyticAt ℂ (e i) 0 ∧
      meromorphicOrderAt (e i) 0 = (sLocalFinitePoleMultiplicity T i.val.1 : WithTop ℤ))
    (b : I(T,ω) → ℂ) (hb : ∀ i, b i = 0 ↔ i.val.1 = j.val.1)
    (C : ℂ) (hC : C ≠ 0)
    (hM : ∀ i, Z(target,i.val.1) =ᶠ[𝓝[≠] 0]
      (fun z ↦ C * e i z / (z + b i) ^ (sLocalFinitePoleMultiplicity T j.val.1 - j.val.2) *
        Z(base,i.val.1) z)) :
    sLocalOrbitalPrincipalPart j ((Kₛ(ω)).mkQ target) ≠ 0 ∧
      ∀ i : I(T,ω), i.val.1 ≠ j.val.1 ∨ i.val.2 < j.val.2 →
        sLocalOrbitalPrincipalPart i ((Kₛ(ω)).mkQ target) = 0 := by
  classical
  let d := sLocalFinitePoleMultiplicity T j.val.1 - j.val.2
  have hZ (i : I(T,ω)) :
      MeromorphicAt Z(base,i.val.1) 0 ∧
        ((-(sLocalRhoPoleOrder i.val.1 : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Z(base,i.val.1) 0 := by
    obtain ⟨χ, s, hc⟩ := sLocalOrbitalPrincipalPart_range_le_ker_chart i.val.1
    exact sLocalOrbitalPrincipalPart_range_le_ker_zeta base χ s _ hc
  have ho (i : I(T,ω)) :
      meromorphicOrderAt Z(target,i.val.1) 0 =
        (sLocalFinitePoleMultiplicity T i.val.1 : WithTop ℤ) -
          (if b i = 0 then (d : WithTop ℤ) else 0) + meromorphicOrderAt Z(base,i.val.1) 0 := by
    have h := orbitalEulerMultiplier_order (he i).1 (hZ i).1 (b i) C hC d (hM i)
    rw [(he i).2] at h
    exact h
  apply orbitalTriangularTest_of_centered_orders ω j target
  · rw [ho, hbase, ite_eq_left ((hb j).mpr rfl)]
    have hr := j.property.2
    have hmr : sLocalFinitePoleMultiplicity T j.val.1 ≤ sLocalRhoPoleOrder j.val.1 := by
      rw [sLocalRhoPoleOrder_eq_card_polePlaces]
      exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
    exact orbitalEulerMultiplier_center_order _ _ _ hr hmr
  · intro i hi
    have hnot : b i ≠ 0 := fun h ↦ hi ((hb i).mp h)
    have horder := ho i
    simp only [ite_eq_right hnot, sub_zero] at horder
    exact (orbitalEulerMultiplier_other_order _ _ _ (hZ i).2).trans_eq horder.symm

local notation "Euler(" v ", " c ")" =>
  (fun z ↦ finiteLocalEulerFactor (Subtype.val v) (sLocalFiniteRestriction v (twistₛ c z)))

private theorem orbitalEuler_reciprocal_shape (v : S) (c : Xₛ) :
    let L := Real.log (v.val.asIdeal.absNorm : ℝ)
    0 < L ∧
      (Euler(v,c)⁻¹ = 1 ∨ ∃ a : ℂ, a ≠ 0 ∧ Euler(v,c)⁻¹ =
        fun z ↦ 1 - a * Complex.exp (-(L : ℂ) * z)) := by
  classical
  intro L
  have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  refine ⟨Real.log_pos hq, ?_⟩
  let ι := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom
  have hunit (z : ℂ) (u : (v.val.adicCompletionIntegers F)ˣ) :
      sLocalFiniteRestriction v (twistₛ c z) (ι u) = sLocalFiniteRestriction v c (ι u) := by
    rw [sLocalOrbitalPrincipalPart_range_le_ker_restrict]
    have hu : ‖((ι u : (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F)‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
          (a := ι u)).mp ⟨u.val.property, u.inv.property⟩)
    rw [hu, Complex.ofReal_one, Complex.one_cpow, mul_one]
  let hv := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.val.adicCompletion F)ˣ := Units.mk0 hv.choose hv.choose_spec.ne_zero
  have hp : ‖π.val‖ = (v.val.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v.val _ hv.choose_spec
  have key (z : ℂ) : (∀ u, sLocalFiniteRestriction v (twistₛ c z) (ι u) = 1) ↔
      (∀ u, sLocalFiniteRestriction v c (ι u) = 1) :=
    forall_congr' fun u ↦ by rw [hunit z u]
  by_cases hu : ∀ u, sLocalFiniteRestriction v c (ι u) = 1
  · right
    refine ⟨sLocalFiniteRestriction v c π, ((Group.isUnit π).map (sLocalFiniteRestriction v c)).ne_zero, ?_⟩
    funext z
    change (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ = _
    unfold finiteLocalEulerFactor
    rw [ite_eq_left ((key z).mpr hu), inv_inv, sLocalOrbitalPrincipalPart_range_le_ker_restrict]
    change 1 - sLocalFiniteRestriction v c π * (‖π.val‖ : ℂ) ^ z = _
    have hp0 : (‖π.val‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr π.ne_zero)
    rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.ofReal_log (norm_nonneg _),
      hp, Real.log_inv, Complex.ofReal_neg]
  · left
    funext z
    change (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ = 1
    unfold finiteLocalEulerFactor
    rw [ite_eq_right (fun h ↦ hu ((key z).mp h)), inv_one]

private theorem orbitalEuler_geometric_order (L a : ℂ) (hL : L ≠ 0) (ha : a ≠ 0) :
    let f := fun z ↦ 1 - a * Complex.exp (-L * z)
    AnalyticAt ℂ f 0 ∧ meromorphicOrderAt f 0 = if a = 1 then 1 else 0 := by
  classical
  intro f
  have hA : AnalyticAt ℂ f 0 := by dsimp [f]; fun_prop
  refine ⟨hA, ?_⟩
  rw [hA.meromorphicOrderAt_eq]
  by_cases h : a = 1
  · have hder : HasDerivAt f (a * L) 0 := by
      have H := (((Complex.hasDerivAt_exp (-L * (0 : ℂ))).comp 0
        ((hasDerivAt_id (0 : ℂ)).const_mul (-L))).const_mul a).const_sub 1
      simpa [f] using H
    have h0 : f 0 = 0 := by simp [f, h]
    rw [ite_eq_left h, hA.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0
      (hder.deriv ▸ mul_ne_zero ha hL), ENat.map_one]
    rfl
  · rw [ite_eq_right h, hA.analyticOrderAt_eq_zero.mpr (show f 0 ≠ 0 from by simpa only [f, mul_zero, Complex.exp_zero, mul_one, sub_ne_zero] using Ne.symm h),
      ENat.map_zero]
    rfl


open Classical in
private theorem orbitalEuler_reciprocal_data (v : S) (c : Xₛ) :
    AnalyticAt ℂ (Euler(v,c)⁻¹) 0 ∧
      meromorphicOrderAt (Euler(v,c)⁻¹) 0 = (if v ∈ sLocalFinitePolePlaces c then 1 else 0) ∧
      (v ∈ sLocalFinitePolePlaces c → Euler(v,c)⁻¹ =
        fun z ↦ 1 - Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * z)) := by
  classical
  obtain ⟨hL, h⟩ := orbitalEuler_reciprocal_shape v c
  have hmem : v ∈ sLocalFinitePolePlaces c ↔ meromorphicOrderAt Euler(v,c) 0 < 0 := by
    simp [sLocalFinitePolePlaces]
  have hb : meromorphicOrderAt Euler(v,c) 0 = -meromorphicOrderAt (Euler(v,c)⁻¹) 0 := by
    rw [← meromorphicOrderAt_inv, inv_inv]
  rcases h with h | ⟨a, ha, h⟩
  · have h1 : AnalyticAt ℂ (Euler(v,c)⁻¹) 0 := by rw [h]; exact analyticAt_const
    have h0 : meromorphicOrderAt (Euler(v,c)⁻¹) 0 = 0 := by
      rw [h]
      change meromorphicOrderAt (fun _ : ℂ ↦ (1 : ℂ)) 0 = _
      simp [meromorphicOrderAt_const]
    have hv : v ∉ sLocalFinitePolePlaces c := by
      rw [hmem, hb, h0, neg_zero]
      exact lt_irrefl _
    exact ⟨h1, by rw [h0, ite_eq_right hv], fun hc ↦ (hv hc).elim⟩
  · obtain ⟨hA, hO⟩ := orbitalEuler_geometric_order _ a (Complex.ofReal_ne_zero.mpr hL.ne') ha
    have ho : meromorphicOrderAt (Euler(v,c)⁻¹) 0 = if a = 1 then 1 else 0 := by rw [h]; exact hO
    have h1 : AnalyticAt ℂ (Euler(v,c)⁻¹) 0 := by rw [h]; exact hA
    have hh : v ∈ sLocalFinitePolePlaces c ↔ a = 1 := by
      rw [hmem, hb, ho]
      by_cases h' : a = 1
      · rw [ite_eq_left h']
        exact iff_of_true (WithTop.coe_lt_coe.mpr (by decide : (-1 : ℤ) < 0)) h'
      · simp [h']
    refine ⟨h1, by simpa only [hh] using ho, fun hp ↦ ?_⟩
    simpa only [hh.mp hp, one_mul] using h

private def orbitalReciprocalProduct (U : Finset S) (c : Xₛ) (z : ℂ) : ℂ :=
  ∏ v ∈ U, (Euler(v,c) z)⁻¹

open Classical in
private theorem orbitalReciprocalProduct_order (T : Finset V) (c : Xₛ) :
    let U := Finset.univ.filter (fun v : S ↦ v.val ∈ T)
    AnalyticAt ℂ (orbitalReciprocalProduct U c) 0 ∧
      meromorphicOrderAt (orbitalReciprocalProduct U c) 0 =
        (sLocalFinitePoleMultiplicity T c : WithTop ℤ) := by
  classical
  intro U
  have ha (v : S) : AnalyticAt ℂ (Euler(v,c)⁻¹) 0 := (orbitalEuler_reciprocal_data v c).1
  refine ⟨U.analyticAt_fun_prod fun v _ ↦ ha v, ?_⟩
  have ho := meromorphicOrderAt_fun_prod (s := U) (f := fun v ↦ Euler(v,c)⁻¹)
    (fun v _ ↦ (ha v).meromorphicAt)
  change meromorphicOrderAt (orbitalReciprocalProduct U c) 0 = _ at ho
  refine ho.trans ?_
  simp_rw [(orbitalEuler_reciprocal_data _ c).2.1]
  unfold U sLocalFinitePoleMultiplicity
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_filter]
  have hP : (Finset.univ.filter fun v : S ↦ v ∈ sLocalFinitePolePlaces c) = sLocalFinitePolePlaces c := by
    ext v
    simp
  let b (v : S) : WithTop ℤ := if v.val ∈ T then 1 else 0
  calc
    _ = ∑ v : S, if v ∈ sLocalFinitePolePlaces c then b v else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ sLocalFinitePolePlaces c <;> by_cases ht : v.val ∈ T <;> simp [b, hv, ht]
    _ = _ := by
      have hh := Finset.sum_filter (s := (Finset.univ : Finset S))
        (p := fun v ↦ v ∈ sLocalFinitePolePlaces c) (f := b)
      simpa only [hP, b] using hh.symm

local notation "ell(" v ")" => (Real.log ((Subtype.val v).asIdeal.absNorm : ℝ))

open Classical in
private theorem orbitalReciprocalProduct_principalValue (U : Finset S) (f : ℬₛ) (c : Xₛ)
    (hT : U.image Subtype.val ⊆ S) :
    Z(sAdelePrincipalValue F hT f,c) =ᶠ[𝓝[≠] 0]
      fun z ↦ orbitalReciprocalProduct U c z * Z(f,c) z := by
  classical
  let T : Finset V := U.image Subtype.val
  obtain ⟨χ, s, hc⟩ := sLocalOrbitalPrincipalPart_range_le_ker_chart c
  have ht : Tendsto (fun z : ℂ ↦ s + z) (𝓝[≠] 0) (𝓝[≠] s) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_const.add continuous_id : Continuous fun z : ℂ ↦ s + z).tendsto'
        (0 : ℂ) s (add_zero s)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact fun h ↦ hz (add_eq_left.mp h)
  have h := nhdsNE_le_codiscrete s (sLocalIdelicZFunction_principalValue T hT f χ)
  filter_upwards [ht.eventually h] with z hz
  simp only [← hc z] at hz
  rw [hz, div_eq_mul_inv, mul_comm, ← Finset.prod_inv_distrib]
  congr 1
  have hU : U = Finset.univ.filter (fun v : S ↦ v.val ∈ T) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun hv ↦ Finset.mem_image.mpr ⟨v, hv, rfl⟩
    · intro hv
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hv
      exact (Subtype.ext heq : w = v) ▸ hw
  rw [orbitalReciprocalProduct, hU, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro v _
  split_ifs <;> simp

private theorem orbitalReciprocalFactor_shift (c₀ c : Xₛ) (b : ℂ) (hc : twistₛ c₀ b = c)
    (v : S) (hv : v ∈ sLocalFinitePolePlaces c₀) (z : ℂ) :
    (1 - Complex.exp (-(ell(v) : ℂ) * (z + b))) = (Euler(v,c) z)⁻¹ := by
  have he := congrFun ((orbitalEuler_reciprocal_data v c₀).2.2 hv) (z + b)
  change (Euler(v,c₀) (z + b))⁻¹ = _ at he
  have hc' : twistₛ c z = twistₛ c₀ (z + b) := by
    rw [← hc]
    exact normTwist_normTwist _ _ _ _ _
  change _ = (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹
  rw [hc']
  exact he.symm

private theorem exists_orbitalReciprocalProduct_divided (D : Finset S) (c₀ : Xₛ)
    (hD : D ⊆ sLocalFinitePolePlaces c₀) (f : ℬₛ) :
    ∃ g : ℬₛ, ∀ (c : Xₛ) (b : ℂ), twistₛ c₀ b = c →
      Z(g,c) =ᶠ[𝓝[≠] 0] fun z ↦
        ((∏ v ∈ D, (ell(v) : ℂ)⁻¹) * orbitalReciprocalProduct D c z) /
          (z + b) ^ D.card * Z(f,c) z := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    exact ⟨f, fun c b _ ↦ .of_forall fun z ↦ by simp [orbitalReciprocalProduct]⟩
  | insert v D hv ih =>
    obtain ⟨g, hg⟩ := ih (Finset.subset_insert _ _ |>.trans hD)
    have hp := hD (Finset.mem_insert_self v D)
    have hL := (orbitalEuler_reciprocal_shape v c₀).1.ne'
    obtain ⟨k, hk⟩ := exists_sLocalMellin_dividedFactor_germ (F := F) (S := S) c₀ hL g
    refine ⟨k, fun c b hc ↦ ?_⟩
    filter_upwards [hg c b hc, hk c b hc] with z hz hz'
    rw [hz', hz, orbitalReciprocalFactor_shift c₀ c b hc v hp]
    simp only [orbitalReciprocalProduct, Finset.prod_insert hv, Finset.card_insert_of_notMem hv,
      pow_succ, div_eq_mul_inv, mul_inv_rev]
    ring

private theorem orbitalNormTwist_zero (c : Xₛ) : twistₛ c 0 = c := by
  ext1 t
  change c t * _ ^ (0 : ℂ) = c t
  rw [Complex.cpow_zero, mul_one]

private theorem orbitalNormTwist_of_same_restriction (c d : Xₛ)
    (h : normOneRestriction mₛ c = normOneRestriction mₛ d) :
    ∃ b : ℂ, twistₛ c b = d := by
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨a, ha, -⟩ := existsUnique_complexPower (c.comp σ)
  obtain ⟨b, hb, -⟩ := existsUnique_complexPower (d.comp σ)
  refine ⟨b - a, ContinuousMonoidHom.ext fun x ↦ ?_⟩
  let t := mₛ x
  let k : J₁ := ⟨x / σ t, by
    change mₛ (x / σ t) = 1
    rw [map_div, hσ, div_self']⟩
  have hk : c k.val = d k.val := DFunLike.congr_fun h k
  have hx : k.val * σ t = x := div_mul_cancel _ _
  have hn : (((t : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr t.ne_zero)
  change c x * (((t : ℝ≥0) : ℝ) : ℂ) ^ (b - a) = d x
  rw [← hx, map_mul, map_mul, hk]
  change d k.val * (c.comp σ) t * _ = d k.val * (d.comp σ) t
  rw [ha, hb, mul_assoc, ← Complex.cpow_add _ _ hn]
  congr 2
  ring

private theorem orbitalReciprocal_lift_shift {T : Finset V} (ω : PontryaginDual J₁) (j : I(T,ω)) :
    ∃ b : I(T,ω) → ℂ, (∀ i, b i = 0 ↔ i.val.1 = j.val.1) ∧
      ∀ i, twistₛ j.val.1 (b i) = i.val.1 := by
  classical
  choose w hw using fun i : I(T,ω) ↦
    orbitalNormTwist_of_same_restriction _ _ (j.property.1.trans i.property.1.symm)
  let b (i : I(T,ω)) := if i.val.1 = j.val.1 then 0 else w i
  have he (i : I(T,ω)) : twistₛ j.val.1 (b i) = i.val.1 := by
    by_cases h : i.val.1 = j.val.1
    · simp only [b, ite_eq_left h]
      exact (orbitalNormTwist_zero j.val.1).trans h.symm
    · simpa only [b, ite_eq_right h] using hw i
  refine ⟨b, fun i ↦ ⟨?_, fun h ↦ ite_eq_left h⟩, he⟩
  intro h
  have h' := he i
  rw [h, orbitalNormTwist_zero] at h'
  exact h'.symm

open Classical in
private theorem exists_orbitalReciprocal_multiplier {T : Finset V} (c₀ : Xₛ) (d : ℕ)
    (hd : d ≤ sLocalFinitePoleMultiplicity T c₀) (f : ℬₛ) :
    let U : Finset S := Finset.univ.filter (fun v : S ↦ v.val ∈ T)
    ∃ C : ℂ, C ≠ 0 ∧ ∃ k : ℬₛ, ∀ (c : Xₛ) (b : ℂ), twistₛ c₀ b = c →
      Z(k,c) =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦
        C * orbitalReciprocalProduct U c z / (z + b) ^ d * Z(f,c) z := by
  classical
  intro U
  let V₀ : Finset S := (sLocalFinitePolePlaces c₀).filter (fun v : S ↦ v.val ∈ T)
  have hd' : d ≤ V₀.card := hd
  obtain ⟨D, hD, hcard⟩ := Finset.exists_subset_card_eq hd'
  have hDV : D ⊆ sLocalFinitePolePlaces c₀ := hD.trans (Finset.filter_subset _ _)
  have hDU : D ⊆ U := fun v hv ↦ Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Finset.mem_filter.mp (hD hv)).2⟩
  obtain ⟨g, hg⟩ := exists_orbitalReciprocalProduct_divided D c₀ hDV f
  let C := ∏ v ∈ D, (ell(v) : ℂ)⁻¹
  have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ inv_ne_zero
    (Complex.ofReal_ne_zero.mpr (orbitalEuler_reciprocal_shape v c₀).1.ne')
  let W := U \ D
  have hW : W.image Subtype.val ⊆ S := by
    intro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.property
  let k := sAdelePrincipalValue F hW g
  refine ⟨C, hC, k, fun c b hc ↦ ?_⟩
  have h' := orbitalReciprocalProduct_principalValue W g c hW
  filter_upwards [h', hg c b hc] with z hz hz'
  have hp : orbitalReciprocalProduct U c z =
      orbitalReciprocalProduct W c z * orbitalReciprocalProduct D c z :=
    (Finset.prod_sdiff hDU).symm
  change Z(k,c) z = _
  change Z(k,c) z = _ at hz
  rw [hz, hz', hp, hcard]
  ring

/-- Realize a nonzero selected coefficient while killing selected coefficients at other
centers and higher selected orders at this center. Start from a standard Gaussian at
the center, then divide the selected reciprocal Euler product by the needed power of
the chart parameter. The divided factors act by compact averages of norm translations. -/
private theorem exists_sLocalOrbitalPrincipalPart_triangular_test {T : Finset V}
    (_hT : T ⊆ S) (_hTne : T.Nonempty) (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial)
    (ω : PontryaginDual J₁) (j : I(T, ω)) :
    ∃ f : ℬₛ,
      sLocalOrbitalPrincipalPart j ((Kₛ(ω)).mkQ f) ≠ 0 ∧
      ∀ i : I(T, ω), i.val.1 ≠ j.val.1 ∨ i.val.2 < j.val.2 →
        sLocalOrbitalPrincipalPart i ((Kₛ(ω)).mkQ f) = 0 := by
  classical
  let c₀ : Xₛ := j.val.1
  have hmul : sLocalFinitePoleMultiplicity T c₀ ≤ sLocalRhoPoleOrder c₀ := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces]
    exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
  have hn := lt_of_le_of_lt (Nat.zero_le _) j.property.2
  obtain ⟨f, hf⟩ := exists_sLocalZeta_full_pole c₀ (hn.trans_le hmul)
  let U : Finset S := Finset.univ.filter (fun v : S ↦ v.val ∈ T)
  let d := sLocalFinitePoleMultiplicity T c₀ - j.val.2
  obtain ⟨C, hC, k, hk⟩ := exists_orbitalReciprocal_multiplier (T := T) c₀ d (Nat.sub_le _ _) f
  obtain ⟨b, hb, hbt⟩ := orbitalReciprocal_lift_shift ω j
  refine ⟨k, orbitalTriangularTest_of_euler_multiplier ω j f k hf
    (fun i ↦ orbitalReciprocalProduct U i.val.1) (fun i ↦ orbitalReciprocalProduct_order T i.val.1)
    b hb C hC (fun i ↦ hk i.val.1 (b i) (hbt i))⟩

end TriangularPrincipalPartTests

open Classical in
/-- Paper: Theorem 7.3.1.2(2), p. 342.
For each selected coefficient there is a homogeneous theta class on which it takes the
value one while every other selected coefficient vanishes.
Deviation: Uses the finite-place selection of part (1). The paper obtains the class from
a test whose zeta transform has a single pole on the component, of the selected order. -/
theorem exists_sLocalOrbitalPrincipalPart_dual {T : Finset V} (_hT : T ⊆ S)
    (_hTne : T.Nonempty) (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial)
    (ω : PontryaginDual J₁) (j : I(T, ω)) :
    ∃ x : Θₛ(ω), ∀ i : I(T, ω),
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) i x =
        if i = j then 1 else 0 := by
  refine sLocalOrbitalPrincipalPart_triangular_dual
    (fun i : I(T, ω) ↦ i.val.1) (fun i ↦ i.val.2) (sLocalFinitePoleMultiplicity T)
    (fun i ↦ (sLocalOrbitalPrincipalPart i).toLinearMap) (fun i ↦ i.property.2) ?_ ?_ j
  · intro i k hc hr
    exact Subtype.ext (Prod.ext hc hr)
  · intro i
    obtain ⟨f, hf, hzero⟩ := exists_sLocalOrbitalPrincipalPart_triangular_test _hT _hTne _hS _hPic ω i
    exact ⟨(Kₛ(ω)).mkQ f, hf, hzero⟩

open Classical in
/-- Paper: Theorem 7.3.1.2(2), p. 341.
The selected coefficients have a biorthogonal family in the quotient. The pairing is
evaluated on a representative of each quotient vector.
Deviation: Uses the finite-place selection of part (1). -/
theorem sLocalOrbitalPrincipalValue_biorthogonal {T : Finset V} (hT : T ⊆ S) (_hTne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁) :
    let R := PV(T, hT, ω)
    ∃ ψ : I(T, ω) → (Θₛ(ω) ⧸ R),
      ∀ (i j : I(T, ω)) (x : Θₛ(ω)), R.mkQ x = ψ j →
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) i x =
          if i = j then 1 else 0 := by
  intro R
  choose y hy using exists_sLocalOrbitalPrincipalPart_dual hT _hTne _hS _hPic ω
  refine ⟨fun j ↦ R.mkQ (y j), fun i j x hx ↦ ?_⟩
  have hmem : x - y j ∈ R := (Submodule.Quotient.eq R).mp hx
  have h0 := sLocalOrbitalPrincipalValue_annihilator_ker hT ω i hmem
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, sub_eq_zero] at h0
  exact h0.trans (hy j i)

/-- Paper: Theorem 7.3.1.2(2), p. 341.
The selected coefficients are topologically free. Two unconditionally convergent series
with the same limit have identical coefficients.
Deviation: Uses the finite-place selection of part (1). -/
theorem sLocalOrbitalPrincipalPart_hasSum_unique {T : Finset V} (_hT : T ⊆ S) (_hTne : T.Nonempty)
    (_hS : IsSaturatedPlaceSet S) (_hPic : PicTrivial) (ω : PontryaginDual J₁)
    (a b : I(T, ω) → ℂ)
    (u : StrongDual ℂ (Θₛ(ω)))
    (ha : HasSum (fun j ↦ a j • sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) j) u)
    (hb : HasSum (fun j ↦ b j • sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) j) u) :
    a = b := by
  classical
  obtain ⟨ψ, hψ⟩ := sLocalOrbitalPrincipalValue_biorthogonal (F := F) (S := S) _hT _hTne _hS _hPic ω
  funext i
  obtain ⟨x, hx⟩ := (PV(T, _hT, ω)).mkQ_surjective (ψ i)
  let ev := ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) x
  have recover (t : I(T, ω) → ℂ)
      (ht : HasSum (fun j ↦ t j • sLocalOrbitalPrincipalPart (F := F) (S := S) (T := T) (ω := ω) j) u) :
      t i = u x := by
    have hs : HasSum (fun j ↦ if j = i then t i else 0) (u x) := by
      refine (ev.hasSum ht).congr_fun fun j ↦ ?_
      change (if j = i then t i else 0) = t j * sLocalOrbitalPrincipalPart j x
      rw [hψ j i x hx]
      by_cases h : j = i <;> simp [h]
    exact (hasSum_ite_eq i (t i)).unique hs
  exact (recover a ha).trans (recover b hb).symm

local notation "Sₚ(" p ")" => sLocalPrimaryPlaces (F := F) S p
local notation "hₚ(" p ")" => sLocalPrimaryPlaces_subset (F := F) S p

/-- Paper: Definition 7.3.1.3, p. 343.
The denominator of the primary orbital quotient is the image of the corresponding
principal-value operator on the homogeneous theta space. -/
def sLocalPrimaryOrbitalSubmodule (p : Vℚ) (ω : PontryaginDual J₁) : Submodule ℂ (Θₛ(ω)) :=
  PV(Sₚ(p), hₚ(p), ω)

local notation "Rₚ(" p ", " ω ")" => sLocalPrimaryOrbitalSubmodule (F := F) (S := S) p ω

/-- Paper: Definition 7.3.1.3, p. 343.
The p-primary orbital quotient is the homogeneous theta space modulo its primary
principal-value image. It carries the quotient topology.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its definition (#5398). -/
def SLocalPrimaryOrbitalQuotient (p : Vℚ) (ω : PontryaginDual J₁) :=
  Θₛ(ω) ⧸ Rₚ(p, ω)

namespace SLocalPrimaryOrbitalQuotient

instance instAddCommGroup (p : Vℚ) (ω : PontryaginDual J₁) :
    AddCommGroup (SLocalPrimaryOrbitalQuotient p ω) :=
  inferInstanceAs (AddCommGroup (Θₛ(ω) ⧸ Rₚ(p, ω)))

instance instModule (p : Vℚ) (ω : PontryaginDual J₁) :
    Module ℂ (SLocalPrimaryOrbitalQuotient p ω) :=
  inferInstanceAs (Module ℂ (Θₛ(ω) ⧸ Rₚ(p, ω)))

instance instTopologicalSpace (p : Vℚ) (ω : PontryaginDual J₁) :
    TopologicalSpace (SLocalPrimaryOrbitalQuotient p ω) :=
  inferInstanceAs (TopologicalSpace (Θₛ(ω) ⧸ Rₚ(p, ω)))

instance instIsTopologicalAddGroup (p : Vℚ) (ω : PontryaginDual J₁) :
    IsTopologicalAddGroup (SLocalPrimaryOrbitalQuotient p ω) :=
  inferInstanceAs (IsTopologicalAddGroup (Θₛ(ω) ⧸ Rₚ(p, ω)))

instance instContinuousSMul (p : Vℚ) (ω : PontryaginDual J₁) :
    ContinuousSMul ℂ (SLocalPrimaryOrbitalQuotient p ω) :=
  inferInstanceAs (ContinuousSMul ℂ (Θₛ(ω) ⧸ Rₚ(p, ω)))

end SLocalPrimaryOrbitalQuotient

local notation "Q(" p ", " ω ")" => SLocalPrimaryOrbitalQuotient (F := F) (S := S) p ω
local notation "π(" p ", " ω ")" => (Rₚ(p, ω)).mkQ

/-- Paper: Definition 7.3.1.3, p. 343.
A theta class represents zero in the p-primary quotient exactly when its selected
highest Laurent coefficients vanish. -/
theorem sLocalPrimaryOrbitalQuotient_mk_eq_zero (p : Vℚ) (_hS : IsSaturatedPlaceSet S)
    (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) (ω : PontryaginDual J₁) (x : Θₛ(ω)) :
    π(p, ω) x = 0 ↔ ∀ j : I(Sₚ(p), ω), sLocalOrbitalPrincipalPart j x = 0 := by
  have h := mem_sLocalOrbitalPrincipalValue_iff (F := F) (S := S) hₚ(p) _hp _hS _hPic ω x
  exact (Submodule.Quotient.mk_eq_zero _).trans h

/-- Paper: Definition 7.3.1.4, p. 343.
The primary multiplicity counts the places over p which contribute a simple pole.
Deviation: Uses positive pole multiplicity and extends it by zero outside the pole locus. -/
def sLocalPrimaryPoleMultiplicity (p : Vℚ) (c : Xₛ) : ℕ :=
  sLocalFinitePoleMultiplicity (Sₚ(p)) c

/-- Paper: Definition 7.3.1.4, p. 343.
Every place in the primary part contributes at the trivial character. -/
theorem sLocalPrimaryPoleMultiplicity_one (p : Vℚ) :
    sLocalPrimaryPoleMultiplicity p (1 : Xₛ) = (Sₚ(p)).card :=
  sLocalFinitePoleMultiplicity_one _ hₚ(p)

section QuotientTransfer

variable {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
variable [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
variable [IsTopologicalAddGroup E₁]
variable [ContinuousSMul ℂ E₁] [ContinuousSMul ℂ E₂]
variable (H₁ : Submodule ℂ E₁) (H₂ : Submodule ℂ E₂)
variable (A : E₁ →L[ℂ] E₂) (A₀ : (E₁ ⧸ H₁) →L[ℂ] (E₂ ⧸ H₂))
variable (x : ℕ → E₂) (d : ℕ → StrongDual ℂ (E₂ ⧸ H₂))
variable (B : Seminorm ℂ (E₂ ⧸ H₂) → ℕ → ℝ≥0) (y : ℕ → E₁)

/-- The induced map of quotients is a linear homeomorphism: it is injective because
`H₁` is the preimage of `H₂`, and open by the open mapping theorem for Fréchet spaces. -/
private theorem orbitalQuotient_lift_equiv (E₁ E₂ : Type*) [AddCommGroup E₁] [Module ℂ E₁]
    [TopologicalSpace E₁] [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℂ E₁] [ContinuousSMul ℂ E₂]
    (H₁ : Submodule ℂ E₁) (H₂ : Submodule ℂ E₂)
    (A : E₁ →L[ℂ] E₂) (A₀ : (E₁ ⧸ H₁) →L[ℂ] (E₂ ⧸ H₂))
    (hF₁ : IsFrechetTVS E₁) (hF₂ : IsFrechetTVS E₂)
    (hH₁ : IsClosed (H₁ : Set E₁)) (hH₂ : IsClosed (H₂ : Set E₂))
    (hpre : H₂.comap A.toLinearMap = H₁)
    (hA₀ : A₀.comp H₁.mkQL = H₂.mkQL.comp A) (hsurj : Surjective A₀) :
    ∃ e : (E₁ ⧸ H₁) ≃L[ℂ] (E₂ ⧸ H₂), e.toContinuousLinearMap = A₀ := by
  have hQ₁ := isFrechetTVS_quotient hF₁ H₁ hH₁
  have hQ₂ := isFrechetTVS_quotient hF₂ H₂ hH₂
  obtain ⟨hadd₂, -, -, -⟩ := hF₂
  let := hadd₂
  obtain ⟨_, _, hmet₁, _⟩ := hQ₁
  have hinj : Injective A₀ := by
    refine (injective_iff_map_eq_zero A₀).mpr fun z hz ↦ ?_
    induction z using Submodule.Quotient.induction_on with
    | _ a =>
    have h2 : H₂.mkQ (A a) = 0 := by
      have := congrArg (fun L : (E₁ →L[ℂ] (E₂ ⧸ H₂)) ↦ L a) hA₀
      exact this.symm.trans hz
    have ha : a ∈ H₁ := hpre ▸ (Submodule.Quotient.mk_eq_zero H₂).mp h2
    exact (Submodule.Quotient.mk_eq_zero H₁).mpr ha
  have hop : IsOpenMap A₀ := isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hQ₂)
    (X := fun _ ↦ E₁ ⧸ H₁) (fun _ ↦ isFrechetTVS_quotient hF₁ H₁ hH₁)
    (fun _ ↦ ContinuousLinearMap.id ℂ (E₁ ⧸ H₁)) (fun _ ↦ Subset.rfl) (fun a ↦ ⟨0, a, rfl⟩) A₀
    hsurj
  let e := LinearEquiv.ofBijective A₀.toLinearMap ⟨hinj, hsurj⟩
  let d : (E₁ ⧸ H₁) ≃L[ℂ] (E₂ ⧸ H₂) :=
    { e with
      continuous_toFun := A₀.continuous
      continuous_invFun := e.toEquiv.continuous_symm_iff.mpr hop }
  exact ⟨d, rfl⟩

/-- Paper: Lemma 7.3.1.5(1), p. 343.
Lifts of the absolute basis vectors give an absolute basis in the first quotient.
Their biorthogonal functionals are an unconditional basis of its strong dual. -/
theorem orbitalQuotient_lift_bases
    (_hF₁ : IsFrechetTVS E₁) (_hF₂ : IsFrechetTVS E₂)
    (_hN₁ : IsNuclearTVS E₁) (_hN₂ : IsNuclearTVS E₂)
    (_hH₁ : IsClosed (H₁ : Set E₁)) (_hH₂ : IsClosed (H₂ : Set E₂))
    (_hA : Injective A) (_hpre : H₂.comap A.toLinearMap = H₁)
    (_hA₀ : A₀.comp H₁.mkQL = H₂.mkQL.comp A) (_hsurj : Surjective A₀)
    (_hb : IsSchauderBasis (H₂.mkQL ∘ x) d) (_habs : SchauderBasis.IsAbsolute (H₂.mkQL ∘ x) d)
    (_hB : ∀ q : Seminorm ℂ (E₂ ⧸ H₂), Continuous q →
      (fun n ↦ q (H₂.mkQL (x n))) =O[atTop] (fun n ↦ (B q n : ℝ)))
    (_hy : ∀ n, A (y n) = x n) :
    let e := H₁.mkQL ∘ y
    let a := fun n ↦ (d n).comp A₀
    let ev : ℕ → StrongDual ℂ (StrongDual ℂ (E₁ ⧸ H₁)) :=
      fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (e n)
    IsSchauderBasis e a ∧ SchauderBasis.IsAbsolute e a ∧
      IsSchauderBasis a ev ∧ SchauderBasis.IsUnconditional a ev := by
  intro e a ev
  let Q₁ := E₁ ⧸ H₁
  let Q₂ := E₂ ⧸ H₂
  have : IsTopologicalAddGroup E₂ := _hF₂.choose
  have hFQ₁ : IsFrechetTVS Q₁ := isFrechetTVS_quotient _hF₁ H₁ _hH₁
  have hFQ₂ : IsFrechetTVS Q₂ := isFrechetTVS_quotient _hF₂ H₂ _hH₂
  have hcomm (v : E₁) : A₀ (H₁.mkQL v) = H₂.mkQL (A v) :=
    DFunLike.congr_fun _hA₀ v
  have hinj : Injective A₀ := by
    intro u v huv
    obtain ⟨u, rfl⟩ := H₁.mkQ_surjective u
    obtain ⟨v, rfl⟩ := H₁.mkQ_surjective v
    apply (Submodule.Quotient.eq H₁).mpr
    rw [← _hpre]
    change A (u - v) ∈ H₂
    rw [map_sub]
    apply (Submodule.Quotient.eq H₂).mp
    exact (hcomm u).symm.trans (huv.trans (hcomm v))
  have : TopologicalSpace.MetrizableSpace Q₁ := hFQ₁.choose_spec.2.1
  have hOpen : IsOpenMap A₀ :=
    isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hFQ₂)
      (X := fun _ ↦ Q₁) (fun _ ↦ hFQ₁) (fun _ ↦ ContinuousLinearMap.id ℂ Q₁)
      (fun _ ↦ Subset.rfl) (fun u ↦ ⟨0, u, rfl⟩) A₀ _hsurj
  let T₀ := LinearEquiv.ofBijective A₀.toLinearMap ⟨hinj, _hsurj⟩
  let T : Q₁ ≃L[ℂ] Q₂ :=
    { T₀ with
      continuous_toFun := A₀.continuous
      continuous_invFun := T₀.toEquiv.continuous_symm_iff.mpr hOpen }
  have hlift (n : ℕ) : T (e n) = H₂.mkQL (x n) := (hcomm (y n)).trans (congrArg H₂.mkQL (_hy n))
  have hcoord (n : ℕ) (v : Q₁) : a n v = d n (T v) := rfl
  have hterm (v : Q₁) (n : ℕ) :
      T.symm (d n (T v) • H₂.mkQL (x n)) = a n v • e n := by
    rw [map_smul, ← hlift, T.symm_apply_apply, hcoord]
  have hb : IsSchauderBasis e a := by
    refine ⟨fun m n ↦ ?_, fun v ↦ ?_⟩
    · change a m (e n) = _
      rw [hcoord, hlift]
      exact _hb.1 m n
    · have hs := (_hb.2 (T v)).mapL T.symm.toContinuousLinearMap
      change HasSum (fun n ↦ T.symm (d n (T v) • H₂.mkQL (x n)))
        (T.symm (T v)) (SummationFilter.conditional ℕ) at hs
      rw [T.symm_apply_apply] at hs
      simp_rw [hterm] at hs
      exact hs
  have ha : SchauderBasis.IsAbsolute e a := by
    intro q hq
    obtain ⟨p, hp, h⟩ := _habs (q.comp T.symm.toLinearMap) (hq.comp T.symm.continuous)
    refine ⟨p.comp T.toLinearMap, hp.comp T.continuous, fun v ↦ ?_⟩
    have hv := h (T v)
    change Summable (fun n ↦ q (T.symm (d n (T v) • H₂.mkQL (x n)))) ∧
      (∑' n, q (T.symm (d n (T v) • H₂.mkQL (x n)))) ≤ p (T v) at hv
    change _ ∧ _ ≤ p (T v)
    simpa only [hterm] using hv
  let : BarrelledSpace ℂ Q₁ := isFrechetTVS_barrelled hFQ₁
  let : PolynormableSpace ℂ Q₁ := hFQ₁.choose_spec.1
  let : UniformSpace Q₁ := IsTopologicalAddGroup.rightUniformSpace Q₁
  let : IsUniformAddGroup Q₁ := isUniformAddGroup_of_addCommGroup
  let hComplete : CompleteSpace Q₁ := hFQ₁.choose_spec.2.2
  let : CompleteSpace Q₁ := hComplete
  have hNQ₁ : IsNuclearTVS Q₁ := isNuclearTVS_quotient _hN₁ H₁
  let : MontelSpace ℂ Q₁ := ⟨fun K hK hbounded ↦ by
    simpa only [hK.closure_eq] using isCompact_closure_of_isNuclearTVS Q₁ hNQ₁ hbounded⟩
  have hReflexive : IsHomeomorph (ContinuousLinearMap.applyₗ (E := Q₁) ℂ (RingHom.id ℂ)) :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨isEmbedding_strongBidual_eval, surjective_strongBidual_eval⟩
  exact ⟨hb, ha, SchauderBasis.isShrinking_of_isAbsolute hComplete hReflexive hb ha,
    SchauderBasis.strongDual_isUnconditional_of_isAbsolute hComplete hReflexive hb ha⟩

/-- Paper: Lemma 7.3.1.5(2), p. 344.
The estimate for each seminorm on the first quotient uses the bound for that
seminorm transported to the second quotient by the inverse induced isomorphism. -/
theorem orbitalQuotient_lift_growth
    (_hF₁ : IsFrechetTVS E₁) (_hF₂ : IsFrechetTVS E₂)
    (_hN₁ : IsNuclearTVS E₁) (_hN₂ : IsNuclearTVS E₂)
    (_hH₁ : IsClosed (H₁ : Set E₁)) (_hH₂ : IsClosed (H₂ : Set E₂))
    (_hA : Injective A) (_hpre : H₂.comap A.toLinearMap = H₁)
    (_hA₀ : A₀.comp H₁.mkQL = H₂.mkQL.comp A) (_hsurj : Surjective A₀)
    (_hb : IsSchauderBasis (H₂.mkQL ∘ x) d) (_habs : SchauderBasis.IsAbsolute (H₂.mkQL ∘ x) d)
    (_hB : ∀ q : Seminorm ℂ (E₂ ⧸ H₂), Continuous q →
      (fun n ↦ q (H₂.mkQL (x n))) =O[atTop] (fun n ↦ (B q n : ℝ)))
    (_hy : ∀ n, A (y n) = x n) :
    ∃ e : (E₁ ⧸ H₁) ≃L[ℂ] (E₂ ⧸ H₂), e.toContinuousLinearMap = A₀ ∧
      ∀ q : Seminorm ℂ (E₁ ⧸ H₁), Continuous q →
        (fun n ↦ q (H₁.mkQL (y n))) =O[atTop]
          (fun n ↦ (B (q.comp e.symm.toLinearMap) n : ℝ)) := by
  obtain ⟨e, he⟩ := orbitalQuotient_lift_equiv E₁ E₂ H₁ H₂ A A₀ _hF₁ _hF₂ _hH₁ _hH₂ _hpre _hA₀
    _hsurj
  refine ⟨e, he, fun q hq ↦ ?_⟩
  have hey (n : ℕ) : H₁.mkQL (y n) = e.symm (H₂.mkQL (x n)) := by
    rw [ContinuousLinearEquiv.eq_symm_apply, ← _hy n]
    change e.toContinuousLinearMap _ = _
    rw [he]
    exact congrArg (fun L : (E₁ →L[ℂ] (E₂ ⧸ H₂)) ↦ L (y n)) _hA₀
  simp only [hey]
  exact _hB (q.comp e.symm.toLinearMap) (hq.comp e.symm.continuous)

end QuotientTransfer

local notation "period(" v ")" => (2 * Real.pi / Real.log ((v : S).val.asIdeal.absNorm : ℝ))
local notation "lattice(" χ ", " v ", " t ", " n ")" =>
  chart(χ) ((((n : ℝ) * period(v) - t : ℝ) : ℂ) * Complex.I)
local notation "phase(" χ ", " v ", " u ", " t ")" =>
  (t ∈ Ico 0 period(v) ∧
    sLocalFiniteRestriction v (chart(χ) (-(t : ℂ) * Complex.I)) u = 1)
local notation "uniformizerNorm(" v ", " u ")" =>
  (‖(↑(u) : (v : S).val.adicCompletion F)‖ = ((v : S).val.asIdeal.absNorm : ℝ)⁻¹)

/-- Paper: Equation (7.3.1.10), p. 344.
There is a unique phase in the given interval for which the adjusted character
is trivial on the chosen local uniformizer. -/
theorem existsUnique_sLocalOrbitalPhase (χ : PontryaginDual Jₛ) (v : S)
    (u : (v.val.adicCompletion F)ˣ) (_hu : uniformizerNorm(v, u)) :
    ∃! t : ℝ, phase(χ, v, u, t) := by
  have hq : (1 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have hq_pos : (0 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := zero_lt_one.trans hq
  have hlog : (0 : ℝ) < Real.log (v.val.asIdeal.absNorm : ℝ) := Real.log_pos hq
  have hqinv_pos : (0 : ℝ) < ((v.val.asIdeal.absNorm : ℝ)⁻¹) := inv_pos.mpr hq_pos
  have hnorm_eq :
      sLocalFiniteRestriction v (chart((1 : PontryaginDual Jₛ)) 1) u =
        (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [sLocalFiniteRestriction_norm v u]
    simpa [Units.map, nnNormHom] using congrArg (fun r : ℝ ↦ (r : ℂ)) _hu
  let eProd := ContinuousMulEquiv.prodUnits
    (InfiniteAdeleRing F) ((w : S) → HeightOneSpectrum.adicCompletion F (Subtype.val w))
  let eFin := ContinuousMulEquiv.piUnits
    (M := fun w : S ↦ HeightOneSpectrum.adicCompletion F (Subtype.val w))
  let g : Jₛ :=
    (QuotientGroup.mk : (SAdeleRing F S)ˣ → Jₛ)
      (eProd.symm (1, eFin.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v u)))
  have hmod : (((mₛ g : ℝ≥0) : ℝ) : ℂ) = (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) := by
    have h1 := hnorm_eq
    change (((1 : PontryaginDual Jₛ) g : Circle) : ℂ) * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at h1
    simpa [Complex.cpow_one] using h1
  have heval (t : ℝ) :
      sLocalFiniteRestriction v (chart(χ) (-(t : ℂ) * Complex.I)) u =
        ((χ g : Circle) : ℂ) *
          Complex.exp (((t * Real.log (v.val.asIdeal.absNorm : ℝ) : ℝ) : ℂ) * Complex.I) := by
    change ((χ g : Circle) : ℂ) * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) = _
    rw [hmod, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqinv_pos.ne')]
    rw [← Complex.ofReal_log hqinv_pos.le, Real.log_inv]
    congr 2
    push_cast
    ring
  let w : ℂ := ((χ g)⁻¹ : Circle)
  have hw_norm : ‖w‖ = 1 := Circle.norm_coe _
  have hw_mul : ((χ g : Circle) : ℂ) * w = 1 := by
    change ((χ g : Circle) : ℂ) * (((χ g)⁻¹ : Circle) : ℂ) = 1
    rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  let θ : ℝ := if 0 ≤ w.arg then w.arg else w.arg + 2 * Real.pi
  have hθ_mem : θ ∈ Ico 0 (2 * Real.pi) := by
    dsimp [θ]
    split_ifs with h
    · exact ⟨h, (Complex.arg_le_pi w).trans_lt (by linarith [Real.pi_pos])⟩
    · have hlt : w.arg < 0 := not_le.mp h
      exact ⟨by linarith [Complex.neg_pi_lt_arg w], by linarith⟩
  have hθ_exp : Complex.exp ((θ : ℂ) * Complex.I) = w := by
    have hbase : Complex.exp ((w.arg : ℂ) * Complex.I) = w := by
      have h := Complex.norm_mul_exp_arg_mul_I w
      rw [hw_norm, Complex.ofReal_one, one_mul] at h
      exact h
    dsimp [θ]
    split_ifs with h
    · exact hbase
    · push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      exact hbase
  refine ⟨θ / Real.log (v.val.asIdeal.absNorm : ℝ), ⟨?_, ?_⟩, ?_⟩
  · constructor
    · exact div_nonneg hθ_mem.1 hlog.le
    · exact div_lt_div_of_pos_right hθ_mem.2 hlog
  · rw [heval, div_mul_cancel₀ _ hlog.ne', hθ_exp, hw_mul]
  · rintro t ⟨ht_mem, ht_eq⟩
    rw [heval] at ht_eq
    have hexp :
        Complex.exp (((t * Real.log (v.val.asIdeal.absNorm : ℝ) : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [hθ_exp]
      exact mul_left_cancel₀ (Circle.coe_ne_zero (χ g)) (ht_eq.trans hw_mul.symm)
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have him : t * Real.log (v.val.asIdeal.absNorm : ℝ) = θ + (k : ℝ) * (2 * Real.pi) := by
      have h := congrArg Complex.im hk
      simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
        Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, add_zero, sub_zero,
        mul_one] at h
      exact h
    have ht_lo : 0 ≤ t * Real.log (v.val.asIdeal.absNorm : ℝ) := mul_nonneg ht_mem.1 hlog.le
    have ht_hi : t * Real.log (v.val.asIdeal.absNorm : ℝ) < 2 * Real.pi :=
      (lt_div_iff₀ hlog).mp ht_mem.2
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hk_lt_mul : (k : ℝ) * (2 * Real.pi) < 1 * (2 * Real.pi) := by
      linarith [hθ_mem.1, ht_hi]
    have hk_gt_mul : (-1 : ℝ) * (2 * Real.pi) < (k : ℝ) * (2 * Real.pi) := by
      linarith [hθ_mem.2, ht_lo]
    have hk_lt : (k : ℝ) < 1 := lt_of_mul_lt_mul_right hk_lt_mul h2pi.le
    have hk_gt : (-1 : ℝ) < (k : ℝ) := lt_of_mul_lt_mul_right hk_gt_mul h2pi.le
    have hk0 : k = 0 := by
      have h1 : k < 1 := Int.cast_lt.mp (by simpa using hk_lt)
      have h2 : -1 < k := Int.cast_lt.mp (by simpa using hk_gt)
      omega
    subst hk0
    simp only [Int.cast_zero, zero_mul, add_zero] at him
    exact (eq_div_iff hlog.ne').mpr him

/-- Paper: Equation (7.3.1.11), p. 344.
At a contributing finite place, the pole on the given component has a unique lattice index. -/
theorem existsUnique_sLocalOrbitalLatticeIndex (χ : PontryaginDual Jₛ) (v : S)
    (u : (v.val.adicCompletion F)ˣ) (_hu : uniformizerNorm(v, u)) (t : ℝ)
    (_ht : phase(χ, v, u, t)) (c : Xₛ)
    (_hc : ∃ s, c = chart(χ) s) (_hv : v ∈ sLocalFinitePolePlaces c) :
    ∃! n : ℤ, c = lattice(χ, v, t, n) := by
  obtain ⟨s, rfl⟩ := _hc
  have hq : (1 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have hq_pos : (0 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := zero_lt_one.trans hq
  have hlog : (0 : ℝ) < Real.log (v.val.asIdeal.absNorm : ℝ) := Real.log_pos hq
  have hqinv_pos : (0 : ℝ) < ((v.val.asIdeal.absNorm : ℝ)⁻¹) := inv_pos.mpr hq_pos
  let eProd := ContinuousMulEquiv.prodUnits
    (InfiniteAdeleRing F) ((w : S) → HeightOneSpectrum.adicCompletion F (Subtype.val w))
  let eFin := ContinuousMulEquiv.piUnits
    (M := fun w : S ↦ HeightOneSpectrum.adicCompletion F (Subtype.val w))
  let finAt : (v.val.adicCompletion F)ˣ → Jₛ := fun x ↦
    (QuotientGroup.mk : (SAdeleRing F S)ˣ → Jₛ)
      (eProd.symm (1, eFin.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x)))
  have hmod_val (x : (v.val.adicCompletion F)ˣ) :
      (((mₛ (finAt x) : ℝ≥0) : ℝ) : ℂ) = ((‖(x : v.val.adicCompletion F)‖ : ℝ) : ℂ) := by
    have h1 := sLocalFiniteRestriction_norm (F := F) (S := S) v x
    change (((1 : PontryaginDual Jₛ) (finAt x) : Circle) : ℂ) *
      (((mₛ (finAt x) : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at h1
    simpa [Complex.cpow_one, Units.map, nnNormHom] using h1
  have htwist_eval (z : ℂ) (x : (v.val.adicCompletion F)ˣ) :
      sLocalFiniteRestriction v (twistₛ (chart(χ) s) z) x =
        sLocalFiniteRestriction v (chart(χ) s) x * ((‖(x : v.val.adicCompletion F)‖ : ℝ) : ℂ) ^ z := by
    change sLocalFiniteRestriction v (chart(χ) s) x * (((mₛ (finAt x) : ℝ≥0) : ℝ) : ℂ) ^ z = _
    rw [hmod_val x]
  have hunr_iff (z : ℂ) :
      (∀ y : (HeightOneSpectrum.adicCompletionIntegers F v.val)ˣ,
          sLocalFiniteRestriction v (twistₛ (chart(χ) s) z)
            (Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom y) = 1) ↔
        (∀ y : (HeightOneSpectrum.adicCompletionIntegers F v.val)ˣ,
          sLocalFiniteRestriction v (chart(χ) s)
            (Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom y) = 1) := by
    have hunit_norm (y : (HeightOneSpectrum.adicCompletionIntegers F v.val)ˣ) :
        ‖((Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom y :
            (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F)‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
          (a := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom y)).mp
          ⟨y.val.property, y.inv.property⟩)
    constructor <;> intro h y
    · have hy := h y
      rw [htwist_eval, hunit_norm y, Complex.ofReal_one, Complex.one_cpow, mul_one] at hy
      exact hy
    · rw [htwist_eval, hunit_norm y, Complex.ofReal_one, Complex.one_cpow, mul_one]
      exact h y
  have hlt : meromorphicOrderAt
      (fun z : ℂ ↦ finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ (chart(χ) s) z))) 0 < 0 :=
    (Finset.mem_filter.mp _hv).2
  have hunr : ∀ y : (HeightOneSpectrum.adicCompletionIntegers F v.val)ˣ,
      sLocalFiniteRestriction v (chart(χ) s)
        (Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom y) = 1 := by
    by_contra hnot
    have hconst : (fun z : ℂ ↦ finiteLocalEulerFactor v.val
        (sLocalFiniteRestriction v (twistₛ (chart(χ) s) z))) = fun _ ↦ (1 : ℂ) := by
      funext z
      unfold finiteLocalEulerFactor
      rw [ite_eq_right (fun hz ↦ hnot ((hunr_iff z).mp hz))]
    rw [hconst] at hlt
    exact not_lt_of_ge (analyticAt_const.meromorphicOrderAt_nonneg) hlt
  let hπ := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.val.adicCompletion F)ˣ := Units.mk0 hπ.choose hπ.choose_spec.ne_zero
  have hπ_norm : ‖(π : v.val.adicCompletion F)‖ = ((v.val.asIdeal.absNorm : ℝ)⁻¹) := by
    have hval : Valued.v (π : v.val.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
      hπ.choose_spec.trans (congrArg Units.val
        (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
          (v.val.valuedAdicCompletion_surjective F)))
    rw [FinitePlace.norm_def, hval, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    simp
  have hratio_norm : ‖((u * π⁻¹ : (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F)‖ = 1 := by
    rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, _hu, hπ_norm]
    exact mul_inv_cancel₀ hqinv_pos.ne'
  have hratio_mem : (u * π⁻¹ : (v.val.adicCompletion F)ˣ).val ∈
        HeightOneSpectrum.adicCompletionIntegers F v.val ∧
      ((u * π⁻¹ : (v.val.adicCompletion F)ˣ)⁻¹).val ∈
        HeightOneSpectrum.adicCompletionIntegers F v.val :=
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := u * π⁻¹)).mpr (Valued.toNormedField.norm_eq_one_iff.mp hratio_norm)
  let y : (HeightOneSpectrum.adicCompletionIntegers F v.val)ˣ :=
    ⟨⟨(u * π⁻¹ : (v.val.adicCompletion F)ˣ).val, hratio_mem.1⟩,
     ⟨((u * π⁻¹ : (v.val.adicCompletion F)ˣ)⁻¹).val, hratio_mem.2⟩,
     Subtype.ext (Units.mul_inv (u * π⁻¹)),
     Subtype.ext (Units.inv_mul (u * π⁻¹))⟩
  have hy_eq : Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom y =
      u * π⁻¹ := by
    ext
    rfl
  have hcu_eq_cπ : sLocalFiniteRestriction v (chart(χ) s) u = sLocalFiniteRestriction v (chart(χ) s) π := by
    have h1 := hunr y
    rw [hy_eq, map_mul, map_inv] at h1
    exact eq_of_mul_inv_eq_one h1
  have hcu : sLocalFiniteRestriction v (chart(χ) s) u = 1 := by
    by_contra hne
    have hfun : (fun z : ℂ ↦ finiteLocalEulerFactor v.val
        (sLocalFiniteRestriction v (twistₛ (chart(χ) s) z))) =
        fun z : ℂ ↦ (1 - sLocalFiniteRestriction v (chart(χ) s) u *
          Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * z))⁻¹ := by
      funext z
      unfold finiteLocalEulerFactor
      rw [ite_eq_left ((hunr_iff z).mpr hunr)]
      change (1 - sLocalFiniteRestriction v (twistₛ (chart(χ) s) z) π)⁻¹ = _
      rw [htwist_eval, hπ_norm, ← hcu_eq_cπ,
        Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqinv_pos.ne'),
        ← Complex.ofReal_log hqinv_pos.le, Real.log_inv]
      push_cast
      rfl
    rw [hfun] at hlt
    have hden_ne : 1 - sLocalFiniteRestriction v (chart(χ) s) u *
        Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * 0) ≠ 0 := by
      simpa [sub_ne_zero] using Ne.symm hne
    have hdiff : Differentiable ℂ (fun z : ℂ ↦ 1 - sLocalFiniteRestriction v (chart(χ) s) u *
        Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * z)) :=
      (differentiable_const 1).sub
        ((differentiable_const _).mul (((differentiable_const _).mul differentiable_id).cexp))
    have han : AnalyticAt ℂ (fun z : ℂ ↦ (1 - sLocalFiniteRestriction v (chart(χ) s) u *
        Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * z))⁻¹) 0 :=
      (hdiff.analyticAt 0).inv hden_ne
    exact not_lt_of_ge han.meromorphicOrderAt_nonneg hlt
  have hmod_u : (((mₛ (finAt u) : ℝ≥0) : ℝ) : ℂ) = (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [hmod_val u, _hu]
  have hcpow_eq : (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) ^ s =
      (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) := by
    have h1 : ((χ (finAt u) : Circle) : ℂ) * (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) ^ s = 1 := by
      rw [← hmod_u]
      exact hcu
    have h2 : ((χ (finAt u) : Circle) : ℂ) *
        (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) = 1 := by
      rw [← hmod_u]
      exact _ht.2
    exact mul_left_cancel₀ (Circle.coe_ne_zero (χ (finAt u))) (h1.trans h2.symm)
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqinv_pos.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqinv_pos.ne'),
    ← Complex.ofReal_log hqinv_pos.le, Real.log_inv] at hcpow_eq
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hcpow_eq
  have hlogC : (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hlog.ne'
  have hs_eq : s = ((((-k : ℤ) : ℝ) * period(v) - t : ℝ) : ℂ) * Complex.I := by
    have hmul : (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)) * s =
        (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)) *
          (((((-k : ℤ) : ℝ) * period(v) - t : ℝ) : ℂ) * Complex.I) := by
      rw [show ((-(Real.log (v.val.asIdeal.absNorm : ℝ)) : ℝ) : ℂ) =
          -(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) by rw [Complex.ofReal_neg]] at hk
      rw [hk]
      simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
        Int.cast_neg, Complex.ofReal_neg, Complex.ofReal_intCast]
      have hdiv : (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) *
          (2 * (Real.pi : ℂ) / (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)) = 2 * (Real.pi : ℂ) :=
        mul_div_cancel₀ _ hlogC
      linear_combination (k : ℂ) * Complex.I * hdiv.symm
    exact mul_left_cancel₀ (neg_ne_zero.mpr hlogC) hmul
  have hinj : Injective (chart(χ)) := by
    intro s₁ s₂ he
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
    let P := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 s₁
    have hs₁ (r : ℝ≥0ˣ) : P r = ((r.val : ℝ) : ℂ) ^ s₁ := one_mul _
    apply (existsUnique_complexPower P).unique hs₁
    intro r
    have h := DFunLike.congr_fun he (σ r)
    change (χ (σ r) : ℂ) * (((mₛ (σ r) : ℝ≥0) : ℝ) : ℂ) ^ s₁ =
      (χ (σ r) : ℂ) * (((mₛ (σ r) : ℝ≥0) : ℝ) : ℂ) ^ s₂ at h
    rw [hσ r] at h
    exact (hs₁ r).trans (mul_left_cancel₀ (Circle.coe_ne_zero _) h)
  refine ⟨-k, ?_, ?_⟩
  · rw [hs_eq]
  · intro n hn
    have h1 := congrArg Complex.im (hinj hn)
    rw [hs_eq] at h1
    simp only [Complex.mul_I_im, Complex.ofReal_re] at h1
    have hper_pos : (0 : ℝ) < period(v) := div_pos (by positivity) hlog
    have hn_cast : (n : ℝ) = ((-k : ℤ) : ℝ) :=
      mul_right_cancel₀ hper_pos.ne' (by linarith)
    exact Int.cast_injective hn_cast

/-- Paper: Discussion after (7.3.1.11), p. 344.
At a common pole, the phase difference is an integer combination of the two local periods.
Deviation: The periods use the residue-field cardinalities of the places. The phase
difference need not be an integer multiple of the period for the rational prime. -/
theorem sLocalOrbitalPhase_sub (χ : PontryaginDual Jₛ) (p : Vℚ)
    (_hS : IsSaturatedPlaceSet S) (v w : S)
    (_hv : v.val ∈ Sₚ(p)) (_hw : w.val ∈ Sₚ(p))
    (uᵥ : (v.val.adicCompletion F)ˣ) (u_w : (w.val.adicCompletion F)ˣ)
    (_hᵥ : uniformizerNorm(v, uᵥ)) (_h_w : uniformizerNorm(w, u_w))
    (tᵥ t_w : ℝ) (_htᵥ : phase(χ, v, uᵥ, tᵥ)) (_ht_w : phase(χ, w, u_w, t_w))
    (c : Xₛ) (_hc : ∃ s, c = chart(χ) s)
    (_hvc : v ∈ sLocalFinitePolePlaces c) (_hwc : w ∈ sLocalFinitePolePlaces c) :
    ∃ a b : ℤ, tᵥ - t_w = (a : ℝ) * period(v) - (b : ℝ) * period(w) := by
  have hinj : Injective (chart(χ)) := by
    intro s t he
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
    let P := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 s
    have hs (u : ℝ≥0ˣ) : P u = ((u.val : ℝ) : ℂ) ^ s := one_mul _
    apply (existsUnique_complexPower P).unique hs
    intro u
    have h := DFunLike.congr_fun he (σ u)
    change (χ (σ u) : ℂ) * (((mₛ (σ u) : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ (σ u) : ℂ) * (((mₛ (σ u) : ℝ≥0) : ℝ) : ℂ) ^ t at h
    rw [hσ u] at h
    exact (hs u).trans (mul_left_cancel₀ (Circle.coe_ne_zero _) h)
  obtain ⟨a, ha⟩ := (existsUnique_sLocalOrbitalLatticeIndex χ v uᵥ _hᵥ tᵥ _htᵥ c _hc _hvc).exists
  obtain ⟨b, hb⟩ := (existsUnique_sLocalOrbitalLatticeIndex χ w u_w _h_w t_w _ht_w c _hc _hwc).exists
  refine ⟨a, b, ?_⟩
  have he := congrArg Complex.im (hinj (ha.symm.trans hb))
  simp only [Complex.mul_I_im, Complex.ofReal_re] at he
  linarith

local notation "fourierZeta(" c ")" =>
  (fun (f : ℬₛ) (z : ℂ) ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
    (dualₛ (twistₛ c z)))

/-- A selected finite pole lies in the closed left half-plane of any unitary chart. -/
private theorem sLocalOrbitalFourierZeta_chart {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) : ∃ (χ : PontryaginDual Jₛ) (a : ℂ),
      j.val.1 = chart(χ) a ∧ a.re ≤ 0 := by
  classical
  obtain ⟨χ, a, ha⟩ := exists_sLocalNormTwist (F := F) (S := S) j.val.1
  refine ⟨χ, a, ha.symm, ?_⟩
  have hm : 0 < sLocalRhoPoleOrder j.val.1 := by
    have hle : sLocalFinitePoleMultiplicity T j.val.1 ≤ sLocalRhoPoleOrder j.val.1 := by
      rw [sLocalRhoPoleOrder_eq_card_polePlaces]
      exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
    exact lt_of_le_of_lt (Nat.zero_le j.val.2) (j.property.2.trans_le hle)
  by_contra h
  have hpos : 0 < a.re := lt_of_not_ge h
  have hA : AnalyticAt ℂ (fun z ↦ sLocalRhoFactor (twistₛ j.val.1 z)) 0 := by
    have h := (sLocalRhoFactor_analyticOn χ a hpos).comp_of_eq
      (f := fun z : ℂ ↦ z + a) (x := 0) (by fun_prop) (zero_add a)
    simpa only [← ha, normTwist_normTwist, Function.comp_def] using h
  have hb : sLocalIdelicOrderBound j.val.1 = 0 :=
    min_eq_left hA.meromorphicOrderAt_nonneg
  simp [sLocalRhoPoleOrder, hb] at hm

/-- On the reflected convergence half-plane, the continued zeta function is analytic. -/
private theorem sLocalOrbitalFourierZeta_analyticOn (χ : PontryaginDual Jₛ) (a : ℂ)
    (f : ℬₛ) : AnalyticOnNhd ℂ
      (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) (1 - (z + a))))
      {z : ℂ | 0 < (1 - (z + a)).re} := by
  have hZ : AnalyticOnNhd ℂ
      (fun s ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) s))
      {s : ℂ | 0 < s.re} :=
    (sLocalIdelicZetaIntegral_analyticOn (sAdeleSchwartzFourier f) χ⁻¹).congr
      (isOpen_Ioi.preimage Complex.continuous_re)
      (fun z hz ↦ (sLocalIdelicZFunction_eq_integral _ ⟨χ⁻¹, z, hz, rfl⟩).symm)
  intro z hz
  exact (hZ _ hz).comp (f := fun w : ℂ ↦ 1 - (w + a)) (by fun_prop)

/-- Paper: Equation (7.3.1.14), p. 344.
The reflected Fourier zeta transform is holomorphic near each selected finite pole
of the correcting factor. Its derivatives therefore evaluate the analytic germ there. -/
theorem sLocalOrbitalFourierZeta_analyticAt {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) (f : ℬₛ) :
    AnalyticAt ℂ (fourierZeta(j.val.1) f) 0 := by
  obtain ⟨χ, a, ha, hle⟩ := sLocalOrbitalFourierZeta_chart j
  have hpos : 0 < (1 - ((0 : ℂ) + a)).re := by simp; linarith
  simpa only [ha, normTwist_normTwist, sLocal_dual_normTwist] using
    sLocalOrbitalFourierZeta_analyticOn χ a f 0 hpos

section

universe u

/-- Difference quotients of continuous functionals give continuous jets on a barrelled space. -/
private theorem orbitalFourierJet_exists_continuousLinear
    {E : Type u} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] (Φ : E → ℂ → ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hΦ : ∀ f, AnalyticOnNhd ℂ (Φ f) U)
    (hbase : ∀ z ∈ U, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z)
    (n : ℕ) {z : ℂ} (hz : z ∈ U) :
    ∃ L : E →L[ℂ] ℂ, ∀ f, L f = iteratedDeriv n (Φ f) z := by
  classical
  have analyticDeriv (f : E) {x : ℂ} (hx : x ∈ U) (k : ℕ) :
      AnalyticAt ℂ (iteratedDeriv k (Φ f)) x := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hΦ f x hx
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  induction n generalizing z with
  | zero => simpa only [iteratedDeriv_zero] using hbase z hz
  | succ n ih =>
    let A (y : ℂ) : E →L[ℂ] ℂ := if hy : y ∈ U then (ih hy).choose else 0
    have hA {y : ℂ} (hy : y ∈ U) (f : E) : A y f = iteratedDeriv n (Φ f) y := by
      simpa only [A, dite_eq_left hy] using (ih hy).choose_spec f
    let D (y : ℂ) := (y - z)⁻¹ • (A y - A z)
    have hlim : Tendsto (fun y f ↦ D y f) (𝓝[≠] z)
        (𝓝 fun f ↦ iteratedDeriv (n + 1) (Φ f) z) := by
      refine tendsto_pi_nhds.mpr fun f ↦ ?_
      rw [iteratedDeriv_succ]
      refine (analyticDeriv f hz n).differentiableAt.hasDerivAt.tendsto_slope.congr' ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz)] with y hy
      simp only [D, smul_apply, sub_apply,
        hA hy, hA hz, slope, vsub_eq_sub]
    exact ⟨continuousLinearMapOfTendsto D hlim, fun _ ↦ rfl⟩

end

/-- Paper: Equation (7.3.1.14), p. 344.
On S-adelic tests the Fourier jet is continuous and complex linear. -/
theorem sLocalOrbitalFourierJet_continuous_linear {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) :
    let D := fun f : ℬₛ ↦ iteratedDeriv j.val.2 (fourierZeta(j.val.1) f) 0
    Continuous D ∧ IsLinearMap ℂ D := by
  obtain ⟨χ, a, ha, hle⟩ := sLocalOrbitalFourierZeta_chart j
  let U := {z : ℂ | 0 < (1 - (z + a)).re}
  let Φ := fun (f : ℬₛ) (z : ℂ) ↦
    sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) (1 - (z + a)))
  have hU : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hzero : (0 : ℂ) ∈ U := by change 0 < (1 - (0 + a)).re; simp; linarith
  have hbase : ∀ z ∈ U, ∃ L : ℬₛ →L[ℂ] ℂ, ∀ f, L f = Φ f z := by
    intro z hz
    obtain ⟨T, hT⟩ := sLocal_fourier_continuousLinear (F := F) (S := S)
    obtain ⟨Z, hZ⟩ := sLocalIdelicZetaIntegral_tempered
      (chart(χ⁻¹) (1 - (z + a))) ⟨χ⁻¹, _, hz, rfl⟩
    refine ⟨Z.comp T, fun f ↦ ?_⟩
    change Z (T f) = _
    rw [hT, hZ]
    exact (sLocalIdelicZFunction_eq_integral _ ⟨χ⁻¹, _, hz, rfl⟩).symm
  let : BarrelledSpace ℂ ℬₛ := (sAdeleSchwartz_montel (F := F) S).1
  obtain ⟨L, hL⟩ := orbitalFourierJet_exists_continuousLinear Φ hU
    (sLocalOrbitalFourierZeta_analyticOn χ a) hbase j.val.2 hzero
  have heq : (fun f : ℬₛ ↦ iteratedDeriv j.val.2 (fourierZeta(j.val.1) f) 0) = L := by
    funext f
    rw [hL]
    simp only [Φ, ha, normTwist_normTwist, sLocal_dual_normTwist]
  change Continuous _ ∧ IsLinearMap ℂ _
  rw [heq]
  exact ⟨L.continuous, L.toLinearMap.isLinear⟩

local notation "fourierJet(" j ")" =>
  (⟨(sLocalOrbitalFourierJet_continuous_linear j).2.mk' _,
    (sLocalOrbitalFourierJet_continuous_linear j).1⟩ : StrongDual ℂ ℬₛ)

/-- A homogeneous theta-kernel test has zero zeta function throughout its component. -/
private theorem orbitalFourierJet_kernel_zeta_zero (ω : PontryaginDual J₁) (c : Xₛ)
    (hc : onComponent(c, ω)) (f : ℬₛ) (hf : f ∈ Kₛ(ω))
    (χ : PontryaginDual Jₛ) (a : ℂ) (ha : chart(χ) a = c) :
    (fun z : ℂ ↦ sLocalIdelicZFunction f (chart(χ) z)) = 0 := by
  have hv := (mem_sLocalHomogeneousAdelicTheta_ker_iff (F := F) (S := S) ω f).mp hf
  have hω := (congrArg (normOneRestriction mₛ) ha).trans hc
  have hr (z : ℂ) (g : J₁) : normOneRestriction mₛ (chart(χ) z) g = (ω g : ℂ) :=
    (normOneRestriction_unitaryChart mₛ (isProperMap_sIdeleQuotientNorm F S).continuous χ z g).trans
      ((normOneRestriction_unitaryChart mₛ (isProperMap_sIdeleQuotientNorm F S).continuous χ a g).symm.trans
        (DFunLike.congr_fun hω g))
  refine eq_of_agree_rightHalf (sLocalIdelicZFunction_meromorphic f χ)
    (fun _ _ ↦ analyticAt_const.meromorphicNFAt) 0 fun z hz ↦ ?_
  let d := (⟨chart(χ) z, sLocalOrderBound_positive χ hz⟩ :
    {q : Xₛ // 0 ≤ sLocalIdelicOrderBound q})
  exact (sLocalIdelicMellin_apply f d).symm.trans (hv d (hr z))

/-- The functional equation transfers identically zero zeta functions to their reflected Fourier germs. -/
private theorem orbitalFourierJet_kernel_reflected_zero (χ : PontryaginDual Jₛ) (f : ℬₛ)
    (hf : (fun z : ℂ ↦ sLocalIdelicZFunction f (chart(χ) z)) = 0) :
    (fun z : ℂ ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) (1 - z)))
      =ᶠ[codiscrete ℂ] 0 := by
  let Z (g : ℬₛ) (η : PontryaginDual Jₛ) (z : ℂ) := sLocalIdelicZFunction g (chart(η) z)
  let R (z : ℂ) := sLocalRhoFactor (chart(χ) z)
  let D (z : ℂ) := Z (sAdeleSchwartzFourier f) χ⁻¹ (1 - z)
  have hZ (g : ℬₛ) (η : PontryaginDual Jₛ) (z : ℂ) : MeromorphicAt (Z g η) z :=
    ((sLocalIdelicZFunction_meromorphic g η) (mem_univ z)).meromorphicAt
  have hEq : Z f χ =ᶠ[codiscrete ℂ] R * D := by
    apply sLocal_meromorphic_identity (hZ f χ) (fun z ↦ (sLocalRhoFactor_meromorphic χ z).mul
      ((hZ _ _ (1 - z)).comp_analyticAt (analyticAt_const.sub analyticAt_id)))
    intro z hz
    have hd : 0 < (1 - z).re := by simp; linarith [hz.2]
    change sLocalIdelicZFunction f (chart(χ) z) =
      R z * sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) (1 - z))
    refine (sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz.1, rfl⟩).trans ?_
    refine (sLocalIdelicZetaIntegral_functionalEquation f χ z hz).trans ?_
    refine (congrArg (fun c ↦ R z * sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) c)
      (sLocal_dual_normTwist χ z)).trans ?_
    exact congrArg (R z * ·)
      (sLocalIdelicZFunction_eq_integral (sAdeleSchwartzFourier f) ⟨χ⁻¹, 1 - z, hd, rfl⟩).symm
  filter_upwards [hEq, sLocalRhoFactor_mul_dual χ] with z hz hprod
  have hr : R z ≠ 0 := left_ne_zero_of_mul
    (hprod.trans_ne ((Group.isUnit (QuotientGroup.mk (-1 : (SAdeleRing F S)ˣ) : Jₛ)).map
      (chart(χ) z)).ne_zero)
  have hzero : R z * D z = 0 := hz.symm.trans (congrFun hf z)
  exact (mul_eq_zero.mp hzero).resolve_left hr

/-- Paper: Equation (7.3.1.14), p. 344.
The Fourier jet annihilates the kernel of the homogeneous theta map. -/
theorem sLocalOrbitalFourierJet_ker {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) :
    Kₛ(ω) ≤ (fourierJet(j)).ker := by
  intro f hf
  obtain ⟨χ, a, ha, _⟩ := sLocalOrbitalFourierZeta_chart j
  have hzero := orbitalFourierJet_kernel_zeta_zero ω j.val.1 j.property.1 f hf χ a ha.symm
  have hcod := orbitalFourierJet_kernel_reflected_zero χ f hzero
  have hshift : Tendsto (fun z : ℂ ↦ z + a) (𝓝[≠] 0) (𝓝[≠] a) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_id.add continuous_const : Continuous fun z : ℂ ↦ z + a).tendsto'
        0 a (zero_add a)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact fun h ↦ hz (add_eq_right.mp h)
  have hev : fourierZeta(j.val.1) f =ᶠ[𝓝[≠] 0] 0 := by
    filter_upwards [hshift.eventually (hcod.filter_mono (nhdsNE_le_codiscrete a))] with z hz
    simpa only [ha, normTwist_normTwist, sLocal_dual_normTwist, Pi.zero_apply] using hz
  have hnhds := (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (sLocalOrbitalFourierZeta_analyticAt j f).continuousAt continuousAt_const).mp hev
  change iteratedDeriv j.val.2 (fourierZeta(j.val.1) f) 0 = 0
  exact (hnhds.iteratedDeriv_eq j.val.2).trans iteratedDeriv_const_zero

/-- Paper: Equations (7.3.1.13)–(7.3.1.14), p. 344.
The indexed Fourier functional is the jet of the reflected zeta transform at its center.
It differentiates in the original norm direction, as in the printed formula. -/
def sLocalOrbitalFourierJet {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) : StrongDual ℂ (Θₛ(ω)) :=
  (Kₛ(ω)).liftQL (fourierJet(j)) (sLocalOrbitalFourierJet_ker j)

/-- Paper: Equation (7.3.1.14), p. 344.
On a test representative the Fourier jet evaluates to the stated derivative. -/
theorem sLocalOrbitalFourierJet_mk {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) (f : ℬₛ) :
    sLocalOrbitalFourierJet j ((Kₛ(ω)).mkQL f) =
      iteratedDeriv j.val.2 (fourierZeta(j.val.1) f) 0 := rfl

local notation "Idx(" p ", " ω ")" => I(Sₚ(p), ω)

section PrimaryBases

/-- Paper: Theorem 7.3.1.6(1), p. 345.
Each primary polar functional vanishes on the primary principal-value image, so
it lies in the image of the transpose of the quotient map. -/
theorem sLocalOrbitalPrincipalPart_range_le_ker
    (p : Vℚ) (ω : PontryaginDual J₁) (j : Idx(p, ω)) :
    Rₚ(p, ω) ≤
      (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j).ker :=
  sLocalOrbitalPrincipalPart_range_le_ker_range ((Kₛ(ω)).mkQ) (Submodule.mkQ_surjective _)
    (sLocalHomogeneousThetaPrincipalValue hₚ(p) ω)
    (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j)
    (sLocalOrbitalPrincipalPart_range_le_ker_test hₚ(p) ω j)

/-- The Fourier functional equation extends meromorphically in each unitary chart. -/
private theorem sLocalOrbitalFourierJet_functionalEquation
    (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    (fun z ↦ sLocalIdelicZFunction f (chart(χ) z)) =ᶠ[codiscrete ℂ]
      (fun z ↦ sLocalRhoFactor (chart(χ) z) *
        sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) (1 - z))) := by
  let R (z : ℂ) := sLocalRhoFactor (chart(χ) z)
  have hZ (w : ℬₛ) (η : PontryaginDual Jₛ) (z : ℂ) :
      MeromorphicAt (fun t ↦ sLocalIdelicZFunction w (chart(η) t)) z :=
    ((sLocalIdelicZFunction_meromorphic w η) (mem_univ z)).meromorphicAt
  apply sLocal_meromorphic_identity (hZ f χ) (fun z ↦ (sLocalRhoFactor_meromorphic χ z).mul
    ((hZ _ _ (1 - z)).comp_analyticAt (analyticAt_const.sub analyticAt_id)))
  intro z hz
  have hd : 0 < (1 - z).re := by simp; linarith [hz.2]
  exact (sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz.1, rfl⟩).trans <|
    (sLocalIdelicZetaIntegral_functionalEquation f χ z hz).trans <|
    (congrArg (fun d ↦ R z * sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) d)
      (sLocal_dual_normTwist χ z)).trans <| congrArg (R z * ·)
      (sLocalIdelicZFunction_eq_integral (sAdeleSchwartzFourier f) ⟨χ⁻¹, 1 - z, hd, rfl⟩).symm

/-- Paper: Theorem 7.3.1.6(1), p. 345.
Each primary Fourier functional vanishes on the primary principal-value image, so
it lies in the image of the transpose of the quotient map. -/
theorem sLocalOrbitalFourierJet_range_le_ker
    (p : Vℚ) (ω : PontryaginDual J₁) (j : Idx(p, ω)) :
    Rₚ(p, ω) ≤
      (sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j).ker := by
  classical
  apply sLocalOrbitalPrincipalPart_range_le_ker_range ((Kₛ(ω)).mkQ) (Submodule.mkQ_surjective _)
    (sLocalHomogeneousThetaPrincipalValue hₚ(p) ω)
    (sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j)
  intro f
  let c := j.val.1
  let g := sAdelePrincipalValue F hₚ(p) f
  rw [show sLocalHomogeneousThetaPrincipalValue hₚ(p) ω ((Kₛ(ω)).mkQ f) =
      (Kₛ(ω)).mkQL g from sLocalHomogeneousThetaPrincipalValue_mk hₚ(p) ω f,
    sLocalOrbitalFourierJet_mk]
  obtain ⟨χ, a, hx, -⟩ := sLocalOrbitalFourierZeta_chart j
  let Q (z : ℂ) := ∏ v : S, if v.val ∈ Sₚ(p) then
    (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹ else 1
  let Z (v : ℬₛ) (η : PontryaginDual Jₛ) (z : ℂ) := sLocalIdelicZFunction v (chart(η) z)
  let R (z : ℂ) := sLocalRhoFactor (chart(χ) z)
  let D (v : ℬₛ) (z : ℂ) := Z (sAdeleSchwartzFourier v) χ⁻¹ (1 - z)
  have heq (v : ℬₛ) : Z v χ =ᶠ[codiscrete ℂ] R * D v :=
    sLocalOrbitalFourierJet_functionalEquation χ v
  have hc : ∀ᶠ z : ℂ in codiscrete ℂ, D g z = D f z *
      ∏ v : S, if v.val ∈ Sₚ(p) then
        (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chart(χ) z)))⁻¹ else 1 := by
    filter_upwards [heq g, heq f, sLocalRhoFactor_mul_dual χ,
      sLocalIdelicZFunction_principalValue Sₚ(p) hₚ(p) f χ] with z hg hf hr hpv
    have hn : R z ≠ 0 := left_ne_zero_of_mul
      (hr.trans_ne ((Group.isUnit (QuotientGroup.mk (-1 : (SAdeleRing F S)ˣ) : Jₛ)).map
        (chart(χ) z)).ne_zero)
    apply mul_left_cancel₀ hn
    rw [← mul_assoc, ← show Z f χ z = R z * D f z from hf,
      ← show Z g χ z = R z * D g z from hg]
    change sLocalIdelicZFunction (sAdelePrincipalValue F hₚ(p) f) _ = sLocalIdelicZFunction f _ * _
    rw [hpv, div_eq_mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    split_ifs <;> simp
  have ht : Tendsto (fun z : ℂ ↦ z + a) (𝓝[≠] 0) (𝓝[≠] a) := by
    have h : Tendsto (fun z : ℂ ↦ z + a) (𝓝[≠] 0) (𝓝[≠] (0 + a)) :=
      ((Homeomorph.addRight a).map_punctured_nhds_eq 0).le
    simpa only [zero_add] using h
  have hprod : fourierZeta(c) g =ᶠ[𝓝[≠] 0] fourierZeta(c) f * Q := by
    filter_upwards [ht.eventually (nhdsNE_le_codiscrete a hc)] with z hz
    simp only [c, hx, Q, normTwist_normTwist, sLocal_dual_normTwist, Pi.mul_apply]
    refine hz.trans (congrArg (D f (z + a) * ·) ?_)
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    split_ifs <;> rfl
  obtain ⟨hQ, horder⟩ := sLocalOrbitalPrincipalPart_range_le_ker_prod Sₚ(p) c
  have hg := sLocalOrbitalFourierZeta_analyticAt j g
  have hf := sLocalOrbitalFourierZeta_analyticAt j f
  have hm : ((sLocalFinitePoleMultiplicity Sₚ(p) c : ℕ) : WithTop ℤ) ≤
      meromorphicOrderAt (fourierZeta(c) g) 0 := by
    rw [meromorphicOrderAt_congr hprod, meromorphicOrderAt_mul hf.meromorphicAt hQ]
    exact horder.trans (le_add_of_nonneg_left hf.meromorphicOrderAt_nonneg)
  have ha : (sLocalFinitePoleMultiplicity Sₚ(p) c : ℕ∞) ≤ analyticOrderAt (fourierZeta(c) g) 0 := by
    rw [hg.meromorphicOrderAt_eq] at hm
    cases ho : analyticOrderAt (fourierZeta(c) g) 0 using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      rw [ho, ENat.map_natCast] at hm
      exact_mod_cast hm
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg).mp ha j.val.2 j.property.2


open Complex Metric in
/-- A nonzero entire function is bounded away from zero on an arbitrarily small circle about each point. -/
private theorem primaryFourier_periodic_sphere {p : ℂ → ℂ} (hp : AnalyticOnNhd ℂ p univ)
    (hne : ∃ z, p z ≠ 0) (δ : ℝ) (hδ : 0 < δ) (c : ℂ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧ ∃ d > (0 : ℝ), ∀ w ∈ sphere c r, d ≤ ‖p w‖ := by
  have hcod := (hp.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
    (fun h ↦ let ⟨z, hz⟩ := hne; hz (h (mem_univ z)))
  obtain ⟨R, hR, hnonzero⟩ := Metric.mem_nhdsWithin_iff.mp (nhdsNE_le_codiscrete c hcod)
  let r := min (R / 2) δ
  have hr : 0 < r := lt_min (half_pos hR) hδ
  have hrR : r < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hex : (sphere c r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere c r).exists_isMinOn hex
    (fun z _ ↦ (hp z trivial).continuousAt.continuousWithinAt.norm)
  have hw' : w ∈ ball c R ∩ {c}ᶜ := by
    rw [mem_sphere] at hw
    exact ⟨mem_ball.mpr (hw.trans_lt hrR), by
      rintro rfl
      exact hr.ne' (by simpa only [dist_self] using hw.symm)⟩
  exact ⟨r, hr, min_le_right _ _, ‖p w‖, norm_pos_iff.mpr (hnonzero hw'), fun z hz ↦ hmin hz⟩

open Complex Metric in
/-- Removing an analytic multiplier periodic in height preserves boundedness on
closed vertical strips inside the half-plane of holomorphy. -/
private theorem primaryFourier_periodic_strip {p f : ℂ → ℂ} {T : ℝ} (hT : 0 < T)
    (hperiod : Periodic p ((T : ℂ) * I)) (hp : AnalyticOnNhd ℂ p univ) (hne : ∃ z, p z ≠ 0)
    (U : Set ℝ) (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' U)) {a b δ : ℝ}
    (hδ : 0 < δ) (hU : Icc (a - δ) (b + δ) ⊆ U)
    (hbound : ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc (a - δ) (b + δ) → ‖p z * f z‖ ≤ C) :
    ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ ≤ C := by
  classical
  let K := Complex.reProdIm (Icc a b) (Icc 0 T)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  choose r hr hr₁ d hd hnorm using primaryFourier_periodic_sphere hp hne δ hδ
  have hcover : K ⊆ ⋃ c : K, ball c.val (r c.val) := fun c hc ↦
    mem_iUnion.mpr ⟨⟨c, hc⟩, mem_ball_self (hr c)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun c : K ↦ ball c.val (r c.val))
    (fun _ ↦ isOpen_ball) hcover
  obtain ⟨C, hC⟩ := hbound
  let M := 1 + ∑ c ∈ s, max C 0 / d c.val
  refine ⟨M, fun z hz ↦ ?_⟩
  let n := ⌊z.im / T⌋
  let v := (n : ℂ) * ((T : ℂ) * I)
  have hvre : v.re = 0 := by simp [v, Complex.mul_re, Complex.mul_im]
  have hvim : v.im = (n : ℝ) * T := by simp [v, Complex.mul_re, Complex.mul_im]
  have hzK : z - v ∈ K := by
    have hfloor := (le_div_iff₀ hT).mp (Int.floor_le (z.im / T))
    have hceil := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (z.im / T))
    change (z - v).re ∈ Icc a b ∧ (z - v).im ∈ Icc 0 T
    rw [Complex.sub_re, hvre, sub_zero, Complex.sub_im, hvim]
    exact ⟨hz, ⟨by dsimp [n]; linarith, by dsimp [n]; linarith⟩⟩
  obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp (hs hzK)
  have hz' : z ∈ ball (c.val + v) (r c.val) := by
    simpa only [mem_ball, dist_eq_norm, sub_add_eq_sub_sub, add_comm c.val] using hzc
  have hc' : c.val.re ∈ Icc a b := c.property.1
  have hsph (w : ℂ) (hw : w ∈ sphere (c.val + v) (r c.val)) : ‖f w‖ ≤ M := by
    have hw₀ : w - v ∈ sphere c.val (r c.val) := by
      simpa only [mem_sphere, dist_eq_norm, sub_add_eq_sub_sub, add_comm c.val] using hw
    have hre : |w.re - c.val.re| ≤ δ := by
      have h := Complex.abs_re_le_norm (w - (c.val + v))
      rw [Complex.sub_re, Complex.add_re, hvre, add_zero, ← dist_eq_norm, mem_sphere.mp hw] at h
      exact h.trans (hr₁ c.val)
    have hwstrip : w.re ∈ Icc (a - δ) (b + δ) := by
      obtain ⟨hlo, hhi⟩ := abs_le.mp hre
      exact ⟨by linarith [hc'.1], by linarith [hc'.2]⟩
    have hper : p w = p (w - v) := by
      simpa only [v, zsmul_eq_mul, sub_add_cancel] using (hperiod.zsmul n (w - v))
    have hpw : d c.val ≤ ‖p w‖ := by rw [hper]; exact hnorm c.val (w - v) hw₀
    have hmul := hC w hwstrip
    rw [norm_mul] at hmul
    calc
      ‖f w‖ ≤ max C 0 / d c.val :=
        (le_div_iff₀ (hd c.val)).2 ((mul_le_mul_of_nonneg_left hpw (norm_nonneg _)).trans
          (by rw [mul_comm]; exact hmul.trans (le_max_left _ _)))
      _ ≤ M := by
        have hsum := Finset.single_le_sum
          (f := fun d' : K ↦ max C 0 / d d'.val)
          (fun i _ ↦ div_nonneg (le_max_right _ _) (hd i.val).le) hc
        dsimp [M]
        linarith
  have hball : closedBall (c.val + v) (r c.val) ⊆ Complex.re ⁻¹' U := by
    intro w hw
    have hre := Complex.abs_re_le_norm (w - (c.val + v))
    rw [Complex.sub_re, Complex.add_re, hvre, add_zero, ← dist_eq_norm] at hre
    obtain ⟨hl, hh⟩ := abs_le.mp (hre.trans ((mem_closedBall.mp hw).trans (hr₁ c.val)))
    exact hU ⟨by linarith [hc'.1], by linarith [hc'.2]⟩
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hf.diffContOnCl_ball hball) ?_
    (subset_closure hz')
  exact fun w hw ↦ hsph w (frontier_ball_subset_sphere hw)


open Complex Metric in
/-- A holomorphic quotient by a finite product of vertical-periodic factors
retains every Schwartz bound on the closed substrips of its domain. -/
private theorem primaryFourier_factors_strip {ι : Type*} (S : Finset ι) (D : ι → ℂ → ℂ)
    (hD : ∀ i ∈ S, Differentiable ℂ (D i) ∧ (∃ z, D i z ≠ 0) ∧
      ∃ T : ℝ, 0 < T ∧ Periodic (D i) ((T : ℂ) * Complex.I))
    {U : Set ℝ} (margin : ∀ a b, a ≤ b → Icc a b ⊆ U →
      ∃ δ > (0 : ℝ), Icc (a - δ) (b + δ) ⊆ U)
    (G : ℂ → ℂ) (hout : EqOn G 0 (Complex.re ⁻¹' U)ᶜ)
    (hG : DifferentiableOn ℂ G (Complex.re ⁻¹' U))
    (hH : (fun z ↦ (∏ i ∈ S, D i z) * G z) ∈ schwartzBergmanSubmodule U) :
    G ∈ schwartzBergmanSubmodule U := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hH
  | @insert i S hi ih =>
    have hrest k (hk : k ∈ S) := hD k (Finset.mem_insert_of_mem hk)
    refine ih hrest ?_
    obtain ⟨hd, hn, T, hT, hper⟩ := hD i (Finset.mem_insert_self _ _)
    let P (z : ℂ) := ∏ k ∈ S, D k z
    have hP : Differentiable ℂ P :=
      Differentiable.fun_finsetProd (fun k hk ↦ (hrest k hk).1)
    refine ⟨fun z hz ↦ by simp [hout hz], hP.differentiableOn.mul hG, ?_⟩
    intro a b hab hsub N
    obtain ⟨δ, hδ, he⟩ := margin a b hab hsub
    have hB := hH.2.2 (a-δ) (b+δ) (by linarith) he N
    obtain ⟨B,hB⟩ := hB
    let g (z : ℂ) := z^N * (P z * G z)
    have hg : DifferentiableOn ℂ g (Complex.re ⁻¹' U) :=
      (differentiableOn_id.pow N).mul (hP.differentiableOn.mul hG)
    obtain ⟨C,hC⟩ := primaryFourier_periodic_strip hT hper (fun z _ ↦ hd.analyticAt z) hn U hg hδ he
      ⟨B, fun z hz ↦ by
        have h := hB ⟨z, hz, rfl⟩
        simpa only [g, P, Finset.prod_insert hi, mul_assoc, mul_left_comm, mul_comm] using h⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact hC z hz

open Complex Metric in
/-- Normalize the meromorphic quotient by an analytic divisor on an open strip.
The upper bound on its pole orders gives holomorphy across all divisor zeros. -/
private theorem primaryFourier_strip_division {ι : Type*} (S : Finset ι) (D : ι → ℂ → ℂ)
    (hD : ∀ i ∈ S, Differentiable ℂ (D i) ∧ (∃ z, D i z ≠ 0) ∧
      ∃ T : ℝ, 0 < T ∧ Periodic (D i) ((T : ℂ) * Complex.I))
    {U : Set ℝ} (hU : IsOpen U) (margin : ∀ a b, a ≤ b → Icc a b ⊆ U →
      ∃ δ > (0 : ℝ), Icc (a - δ) (b + δ) ⊆ U)
    (H : SchwartzBergman U)
    (hord : ∀ z ∈ Complex.re ⁻¹' U, meromorphicOrderAt (fun z ↦ ∏ i ∈ S, D i z) z ≤
      meromorphicOrderAt H.val z) :
    ∃ G : SchwartzBergman U, ∀ z, (∏ i ∈ S, D i z) * G.val z = H.val z := by
  let stripDomain := Complex.re ⁻¹' U
  let P (z : ℂ) := ∏ i ∈ S, D i z
  have hV : IsOpen stripDomain := hU.preimage Complex.continuous_re
  have hP : Differentiable ℂ P :=
    Differentiable.fun_finsetProd (fun i hi ↦ (hD i hi).1)
  have hevent (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, P w ≠ 0 := by
    have single i (hi : i ∈ S) : ∀ᶠ w in 𝓝[≠] z, D i w ≠ 0 := by
      have hd : AnalyticOnNhd ℂ (D i) univ := fun u _ ↦ (hD i hi).1.analyticAt u
      have h := hd.eqOn_zero_or_eventually_ne_zero_of_preconnected
        isPreconnected_univ
      obtain ⟨u,hu⟩ := (hD i hi).2.1
      exact nhdsNE_le_codiscrete z (h.resolve_left (fun h0 ↦ hu (h0 (mem_univ u))))
    filter_upwards [(S.eventually_all.mpr single)] with w hw
    exact Finset.prod_ne_zero_iff.mpr hw
  have ha (z : ℂ) (hz : z ∈ stripDomain) : AnalyticAt ℂ H.val z :=
    H.property.2.1.analyticOnNhd hV z hz
  have hm : MeromorphicOn (H.val / P) stripDomain :=
    fun z hz ↦ (ha z hz).meromorphicAt.div (hP.analyticAt z).meromorphicAt
  let G := toMeromorphicNFOn (H.val / P) stripDomain
  have hnorm : MeromorphicNFOn G stripDomain := meromorphicNFOn_toMeromorphicNFOn _ _
  have hG (z : ℂ) (hz : z ∈ stripDomain) : AnalyticAt ℂ G z := by
    apply (hnorm hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    change 0 ≤ meromorphicOrderAt (toMeromorphicNFOn _ _) _
    rw [meromorphicOrderAt_toMeromorphicNFOn hm hz,
      meromorphicOrderAt_div (ha z hz).meromorphicAt (hP.analyticAt z).meromorphicAt]
    have hfinite := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (hP.analyticAt z).meromorphicAt).mpr (hevent z)
    have hle := hord z hz
    change meromorphicOrderAt P z ≤ _ at hle
    cases h : meromorphicOrderAt P z using WithTop.recTopCoe with
    | top => exact (hfinite h).elim
    | coe a =>
      cases hi : meromorphicOrderAt H.val z using WithTop.recTopCoe with
      | top => simp
      | coe b =>
        rw [h,hi] at hle
        exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (WithTop.coe_le_coe.mp hle))
  have hout : EqOn G 0 stripDomainᶜ := by
    intro z hz
    change G z = 0
    rw [show G z = H.val z / P z from toMeromorphicNFOn_eq_self_on_compl hm hz,
      show H.val z = 0 from H.property.1 hz, zero_div]
  have he (z : ℂ) : P z * G z = H.val z := by
    by_cases hz : z ∈ stripDomain
    · have hev : (fun w ↦ P w * G w) =ᶠ[𝓝[≠] z] H.val := by
        filter_upwards [hm.toMeromorphicNFOn_eq_self_on_nhdsNE hz, hevent z] with w hq hw
        change G w = H.val w / P w at hq
        rw [hq, mul_div_cancel₀ _ hw]
      exact tendsto_nhds_unique (((hP.continuous.continuousAt.mul (hG z hz).continuousAt).tendsto.mono_left
        (nhdsWithin_le_nhds (s := {z}ᶜ))).congr' hev)
        ((ha z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    · rw [show G z = 0 from hout hz, mul_zero, show H.val z = 0 from H.property.1 hz]
  have hmem : (fun z ↦ (∏ i ∈ S, D i z) * G z) ∈ schwartzBergmanSubmodule U := by
    rw [show (fun z ↦ (∏ i ∈ S, D i z) * G z) = H.val from funext he]
    exact H.property
  refine ⟨⟨G, primaryFourier_factors_strip S D hD margin G hout
      (fun z hz ↦ (hG z hz).differentiableAt.differentiableWithinAt) hmem⟩, he⟩

/-- Every reciprocal finite Euler factor is entire, nonzero somewhere, and periodic in the imaginary direction. -/
private theorem primaryFourier_factor_data (v : S) (c : Xₛ) :
    let D (z : ℂ) := (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)))⁻¹
    Differentiable ℂ D ∧ (∃ z, D z ≠ 0) ∧
      ∃ T : ℝ, 0 < T ∧ Periodic D ((T : ℂ) * Complex.I) := by
  have h := orbitalEuler_reciprocal_shape (F := F) v c
  intro D
  let L := Real.log (v.val.asIdeal.absNorm : ℝ)
  have hL : 0 < L := h.1
  rcases h.2 with h | ⟨a, ha, h⟩
  · have hconst : D = fun _ ↦ 1 := h
    rw [hconst]
    exact ⟨differentiable_const _, ⟨0, one_ne_zero⟩, 1, zero_lt_one, fun _ ↦ rfl⟩
  · have hform : D = fun z ↦ 1 - a * Complex.exp (-(L : ℂ) * z) := h
    rw [hform]
    let T := 2 * Real.pi / L
    have hT : 0 < T := div_pos (by positivity) hL
    have halg : -(L : ℂ) * ((T : ℂ) * Complex.I) = -(2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp [T]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
    refine ⟨by fun_prop, ?_, T, hT, fun z ↦ ?_⟩
    · by_cases h₀ : a = 1
      · refine ⟨1, ?_⟩
        change 1 - a * Complex.exp (-(L : ℂ) * 1) ≠ 0
        rw [h₀, one_mul, mul_one, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
        exact sub_ne_zero.mpr (by exact_mod_cast (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hL)).ne')
      · exact ⟨0, by simpa using sub_ne_zero.mpr (Ne.symm h₀)⟩
    · change 1 - a * Complex.exp (-(L : ℂ) * (z + _)) = 1 - a * Complex.exp (-(L : ℂ) * z)
      rw [mul_add, Complex.exp_add, halg, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]

open Classical in
/-- The vanishing order of the finite Euler denominator is the sum of the local simple-pole multiplicities. -/
private theorem primaryFourier_divisor_order (T : Finset V) (χ : PontryaginDual Jₛ) (z : ℂ) :
    let U := Finset.univ.filter (fun v : S ↦ v.val ∈ T)
    meromorphicOrderAt (orbitalReciprocalProduct (F := F) (S := S) U ((circleToComplex).comp χ)) z =
      (sLocalFinitePoleMultiplicity (F := F) (S := S) T (chart(χ) z) : WithTop ℤ) := by
  classical
  intro U
  let b := (circleToComplex).comp χ
  have hs : orbitalReciprocalProduct U (chart(χ) z) = orbitalReciprocalProduct U b ∘ (· + z) := by
    funext w
    apply Finset.prod_congr rfl
    intro v _
    change (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ (chart(χ) z) w)))⁻¹ =
      (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ b (w + z))))⁻¹
    rw [normTwist_normTwist]
  have ho := (orbitalReciprocalProduct_order (F := F) (S := S) T (chart(χ) z)).2
  change meromorphicOrderAt (orbitalReciprocalProduct U (chart(χ) z)) 0 = _ at ho
  rw [hs, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add] at ho
  exact ho

/-- Finite Euler denominators have no zeros in the right half-plane of a unitary chart. -/
private theorem primaryFourier_right_multiplicity_zero (T : Finset V) (χ : PontryaginDual Jₛ)
    (z : ℂ) (hz : 0 < z.re) : sLocalFinitePoleMultiplicity (F := F) (S := S) T (chart(χ) z) = 0 := by
  classical
  let c := chart(χ) z
  have hA : AnalyticAt ℂ (fun t ↦ sLocalRhoFactor (twistₛ c t)) 0 := by
    have h := (sLocalRhoFactor_analyticOn χ z hz).comp_of_eq
      (f := fun t : ℂ ↦ t + z) (x := 0) (by fun_prop) (zero_add z)
    simpa only [c, normTwist_normTwist, Function.comp_def] using h
  have hb : sLocalIdelicOrderBound c = 0 := min_eq_left hA.meromorphicOrderAt_nonneg
  have hle : sLocalFinitePoleMultiplicity (F := F) (S := S) T c ≤ sLocalRhoPoleOrder c := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces]
    exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
  exact Nat.eq_zero_of_le_zero (by simpa [sLocalRhoPoleOrder, hb] using hle)
/-- Vanishing Fourier jets give the orders required for division of the reflected coordinate on its half-plane. -/
private theorem primaryFourier_left_order (T : Finset V) (χ : PontryaginDual Jₛ) (f : ℬₛ)
    : let ω := χ.comp (⟨(mₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ)
    (∀ j : I(T,ω), sLocalOrbitalFourierJet (F := F) (S := S) (T := T)
      (ω := ω) j ((Kₛ(ω)).mkQ f) = 0) →
    ∀ (z : ℂ), z.re < 1 →
    (sLocalFinitePoleMultiplicity (F := F) (S := S) T (chart(χ) z) : WithTop ℤ) ≤
      meromorphicOrderAt (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).2.val z := by
  classical
  intro ω hf z hz
  let c := chart(χ) z
  let k := sLocalFinitePoleMultiplicity (F := F) (S := S) T c
  let H := (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).2
  have hH : AnalyticAt ℂ H.val z :=
    H.property.2.1.analyticOnNhd (isOpen_Iio.preimage Complex.continuous_re) z hz
  change (k : WithTop ℤ) ≤ meromorphicOrderAt H.val z
  by_cases hk : k = 0
  · exact (congrArg (fun n : ℕ ↦ (n : WithTop ℤ)) hk).trans_le hH.meromorphicOrderAt_nonneg
  have hc : onComponent(c,ω) := by
    apply ContinuousMonoidHom.ext
    intro u
    change (χ u.val : ℂ) * ((((mₛ u.val).val : ℝ) : ℂ) ^ z) = (χ u.val : ℂ)
    rw [show mₛ u.val = 1 from u.property]
    simp
  let j₀ : I(T, ω) := ⟨(c,0),hc,Nat.pos_of_ne_zero hk⟩
  let D := fourierZeta(c) f
  have hD : AnalyticAt ℂ D 0 := sLocalOrbitalFourierZeta_analyticAt (F := F) (S := S) j₀ f
  have hDa : (k : ℕ∞) ≤ analyticOrderAt D 0 := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hD).mpr
    intro r hr
    let j : I(T, ω) := ⟨(c,r),hc,hr⟩
    exact (sLocalOrbitalFourierJet_mk (F := F) (S := S) j f).symm.trans (hf j)
  have hDo : (k : WithTop ℤ) ≤ meromorphicOrderAt D 0 := by
    rw [hD.meromorphicOrderAt_eq]
    cases ho : analyticOrderAt D 0 using ENat.recTopCoe with
    | top => simp
    | coe n =>
      rw [ENat.map_natCast]
      rw [ho] at hDa
      exact_mod_cast hDa
  have hopen : IsOpen {w : ℂ | (w + z).re < 1} :=
    isOpen_lt (Complex.continuous_re.comp (continuous_id.add continuous_const)) continuous_const
  have hnear := hopen.mem_nhds (show (0 : ℂ) ∈ {w : ℂ | (w + z).re < 1} by simpa using hz)
  have he : (fun w : ℂ ↦ H.val (w+z)) =ᶠ[𝓝 (0 : ℂ)] D := by
    filter_upwards [hnear] with w hw
    change H.val (w+z) = sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (twistₛ c w))
    simpa only [H, c, normTwist_normTwist, sLocal_dual_normTwist] using
      (sLocalZetaPair_mk (F := F) (S := S) χ f).2 (show (w + z).re < 1 from hw)
  have h := meromorphicOrderAt_congr (he.symm.filter_mono nhdsWithin_le_nhds)
  rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt, zero_add] at h
  exact hDo.trans_eq h

/-- The right-hand zeta datum in a single unitary chart determines the homogeneous theta class. -/
private theorem primaryFourier_right_separates (χ : PontryaginDual Jₛ) (f g : ℬₛ)
    (h : ∀ z : ℂ, 0 < z.re → sLocalIdelicZFunction f (chart(χ) z) =
      sLocalIdelicZFunction g (chart(χ) z)) :
    let ω := χ.comp (⟨(mₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ)
    (Kₛ(ω)).mkQ f = (Kₛ(ω)).mkQ g := by
  intro ω
  have hall := eq_of_agree_rightHalf (sLocalIdelicZFunction_meromorphic f χ)
    (sLocalIdelicZFunction_meromorphic g χ) 0 h
  apply (Submodule.Quotient.eq _).mpr
  apply (mem_sLocalHomogeneousAdelicTheta_ker_iff (F := F) (S := S) ω _).mpr
  intro c hc
  obtain ⟨z,hz⟩ := orbitalNormTwist_of_same_restriction ((circleToComplex).comp χ) c.val
    (ContinuousMonoidHom.ext fun k ↦ (hc k).symm)
  rw [map_sub]
  change sLocalIdelicZFunction f c.val - sLocalIdelicZFunction g c.val = 0
  exact sub_eq_zero.mpr (hz ▸ congrFun hall z)

open Classical in
/-- Taking principal value multiplies the right zeta coordinate by the finite Euler denominator. -/
private theorem primaryFourier_principalValue_right {T : Finset V} (hT : T ⊆ S)
    (χ : PontryaginDual Jₛ) (f : ℬₛ) (z : ℂ) (hz : 0 < z.re) :
    let U := Finset.univ.filter (fun v : S ↦ v.val ∈ T)
    sLocalIdelicZFunction (sAdelePrincipalValue F hT f) (chart(χ) z) =
      (orbitalReciprocalProduct (F := F) (S := S) U ((circleToComplex).comp χ) z) *
        sLocalIdelicZFunction f (chart(χ) z) := by
  classical
  intro U
  let Z (f : ℬₛ) := (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).1
  let P := orbitalReciprocalProduct (F := F) (S := S) U ((circleToComplex).comp χ)
  have hP : Differentiable ℂ P := Differentiable.fun_finsetProd fun v hv ↦
    (primaryFourier_factor_data (F := F) (S := S) v ((circleToComplex).comp χ)).1
  have hright : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hZ (g : ℬₛ) : ContinuousAt (Z g).val z :=
    (Z g).property.2.1.continuousOn.continuousAt (hright.mem_nhds hz)
  have he : (Z (sAdelePrincipalValue F hT f)).val =ᶠ[𝓝[≠] z] fun w ↦ P w * (Z f).val w := by
    have hnb : ∀ᶠ w : ℂ in 𝓝[≠] z, 0 < w.re :=
      mem_of_superset (nhdsWithin_le_nhds (hright.mem_nhds hz)) (fun _ h ↦ h)
    filter_upwards [nhdsNE_le_codiscrete z (sLocalIdelicZFunction_principalValue T hT f χ),
      hnb] with w hw hpos
    rw [(sLocalZetaPair_mk χ _).1 hpos, (sLocalZetaPair_mk χ f).1 hpos]
    change sLocalIdelicZFunction _ (chart(χ) w) = P w * sLocalIdelicZFunction f (chart(χ) w)
    rw [hw]
    rw [div_eq_mul_inv, mul_comm, ← Finset.prod_inv_distrib]
    congr 1
    change _ = ∏ v ∈ (Finset.univ.filter fun v : S ↦ v.val ∈ T), (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chart(χ) w)))⁻¹
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro v _
    split_ifs <;> simp
  have hp : (Z (sAdelePrincipalValue F hT f)).val z = P z * (Z f).val z :=
    tendsto_nhds_unique ((hZ _).tendsto.mono_left nhdsWithin_le_nhds)
      (((hP.continuous.continuousAt.mul (hZ f)).tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
  exact ((sLocalZetaPair_mk χ _).1 hz).symm.trans
    (hp.trans (congrArg (P z * ·) ((sLocalZetaPair_mk χ f).1 hz)))

open Classical in
/-- Divide both components by the finite Euler denominator and realize the resulting matching pair locally. -/
private theorem primaryFourier_local_range {T : Finset V} (hT : T ⊆ S)
    (χ : PontryaginDual Jₛ) (f : ℬₛ)
    : let ω := χ.comp (⟨(mₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ)
    (∀ j : I(T,ω), sLocalOrbitalFourierJet (F := F) (S := S) (T := T)
      (ω := ω) j ((Kₛ(ω)).mkQ f) = 0) →
    (Kₛ(ω)).mkQ f ∈ PV(T, hT, ω) := by
  classical
  intro ω hf
  let U := Finset.univ.filter (fun v : S ↦ v.val ∈ T)
  let b := (circleToComplex).comp χ
  let D (v : S) (z : ℂ) := (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ b z)))⁻¹
  let P (z : ℂ) := ∏ v ∈ U, D v z
  have hD v (_ : v ∈ U) := primaryFourier_factor_data (F := F) (S := S) v b
  have hP : Differentiable ℂ P := Differentiable.fun_finsetProd fun v hv ↦ (hD v hv).1
  let H := sLocalZetaPair (F := F) (S := S) χ ((Kₛ(ω)).mkQ f)
  have ho (z : ℂ) : meromorphicOrderAt P z =
      (sLocalFinitePoleMultiplicity (F := F) (S := S) T (chart(χ) z) : WithTop ℤ) :=
    primaryFourier_divisor_order (F := F) (S := S) T χ z
  have hpos (z : ℂ) (hz : 0 < z.re) : meromorphicOrderAt P z = 0 := by
    rw [ho, primaryFourier_right_multiplicity_zero T χ z hz, Nat.cast_zero]
  have hright a b (hab : a ≤ b) (hs : Icc a b ⊆ Ioi 0) :
      ∃ δ > (0 : ℝ), Icc (a - δ) (b + δ) ⊆ Ioi 0 := by
    have ha : 0 < a := hs (left_mem_Icc.mpr hab)
    exact ⟨a/2, half_pos ha, fun x hx ↦ by
      change 0 < x
      linarith [hx.1]⟩
  have hleft a b (hab : a ≤ b) (hs : Icc a b ⊆ Iio 1) :
      ∃ δ > (0 : ℝ), Icc (a - δ) (b + δ) ⊆ Iio 1 := by
    have hb : b < 1 := hs (right_mem_Icc.mpr hab)
    exact ⟨(1-b)/2, by linarith, fun x hx ↦ by
      change x < 1
      linarith [hx.2]⟩
  obtain ⟨G₁, h₁⟩ := primaryFourier_strip_division U D hD isOpen_Ioi hright H.1
    (fun z hz ↦ (hpos z hz).trans_le
      (H.1.property.2.1.analyticOnNhd (isOpen_Ioi.preimage Complex.continuous_re) z hz).meromorphicOrderAt_nonneg)
  obtain ⟨G₂, h₂⟩ := primaryFourier_strip_division U D hD isOpen_Iio hleft H.2
    (fun z hz ↦ (ho z).trans_le (primaryFourier_left_order (F := F) (S := S) T χ f hf z hz))
  have hH : H ∈ sLocalZetaMatching (F := F) (S := S) χ := by
    rw [← sLocalZetaPair_range]
    exact ⟨_, rfl⟩
  have hm := (mem_sLocalZetaMatching (F := F) (S := S) χ H).mp hH
  have hG : (G₁, G₂) ∈ (sLocalZetaPair (F := F) (S := S) χ).range := by
    rw [sLocalZetaPair_range, mem_sLocalZetaMatching]
    intro z hz
    have hn : P z ≠ 0 :=
      (hP.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp (hpos z hz.1)
    apply mul_left_cancel₀ hn
    change P z * G₁.val z = P z * (sLocalRhoFactor (chart(χ) z) * G₂.val z)
    calc
      P z * G₁.val z = H.1.val z := h₁ z
      _ = sLocalRhoFactor (chart(χ) z) * H.2.val z := hm hz
      _ = _ := by rw [← h₂ z]; exact mul_left_comm _ _ _
  obtain ⟨x,hx⟩ := hG
  obtain ⟨g,rfl⟩ := (Kₛ(ω)).mkQ_surjective x
  refine ⟨(Kₛ(ω)).mkQ g, (sLocalHomogeneousThetaPrincipalValue_mk hT ω g).trans ?_⟩
  apply primaryFourier_right_separates χ
  intro z hz
  have hg := congrArg (fun p : SchwartzBergman (Ioi 0) × SchwartzBergman (Iio 1) ↦ p.1.val z) hx
  calc
    sLocalIdelicZFunction (sAdelePrincipalValue F hT g) (chart(χ) z) =
        P z * sLocalIdelicZFunction g (chart(χ) z) :=
      primaryFourier_principalValue_right (F := F) (S := S) hT χ g z hz
    _ = P z * G₁.val z := congrArg (P z * ·) (((sLocalZetaPair_mk χ g).1 hz).symm.trans hg)
    _ = H.1.val z := h₁ z
    _ = sLocalIdelicZFunction f (chart(χ) z) := (sLocalZetaPair_mk χ f).1 hz

/-- The common kernel of the selected Fourier jets is the primary principal-value image. -/
private theorem sLocalOrbitalFourierJet_commonKer
    (p : Vℚ) (ω : PontryaginDual J₁) (hS : IsSaturatedPlaceSet S)
    (hp : (Sₚ(p)).Nonempty) (hPic : PicTrivial) (x : Θₛ(ω)) :
    x ∈ Rₚ(p, ω) ↔ ∀ j : Idx(p, ω), sLocalOrbitalFourierJet j x = 0 := by
  classical
  refine ⟨fun hx j ↦ (sLocalOrbitalFourierJet_range_le_ker p ω j) hx, ?_⟩
  obtain ⟨τ,hτ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨χ,hχ,-⟩ := (existsUnique_sLocalNormSectionCharacter (F := F) (S := S) τ hτ ω).exists
  have e : χ.comp (⟨(mₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ) = ω :=
    hχ
  subst ω
  obtain ⟨f,rfl⟩ := (Kₛ(_)).mkQ_surjective x
  exact primaryFourier_local_range (F := F) (S := S) hₚ(p) χ f

/-- a unitary chart covers exactly the chosen norm-one component. -/
private theorem sLocalOrbitalIndex_enumerable_or_empty_chart
    {F : Type*} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (ω : PontryaginDual (((sIdeleQuotientNorm F S)).ker)) :
    ∃ χ : PontryaginDual (SIdeleQuotient F S),
      (∀ z : ℂ, (normOneRestriction (sIdeleQuotientNorm F S) (((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) z) = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω)) ∧
      ∀ d : (QuasiCharacter (SIdeleQuotient F S)), (normOneRestriction (sIdeleQuotientNorm F S) d = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω) → ∃ z : ℂ, ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) z = d := by
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨χ, hu, ht⟩ := exists_character_on_split (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous σ hσ ω 1
  refine ⟨χ, fun z ↦ ContinuousMonoidHom.ext fun u ↦
    (normOneRestriction_unitaryChart (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous χ z u).trans
      (congrArg Subtype.val (hu u)), ?_⟩
  intro d hd
  obtain ⟨z, hz, -⟩ := existsUnique_complexPower (d.comp σ)
  refine ⟨z, ContinuousMonoidHom.ext fun g ↦ ?_⟩
  let t := (sIdeleQuotientNorm F S) g
  let k : (((sIdeleQuotientNorm F S)).ker) := ⟨g / σ t, by change (sIdeleQuotientNorm F S) (g / σ t) = 1; rw [map_div, hσ]; exact div_self' _⟩
  have hg : k.val * σ t = g := div_mul_cancel _ _
  have hχg : χ g = ω k := by
    calc χ g = χ k.val * χ (σ t) := (congrArg χ hg.symm).trans (map_mul χ _ _)
         _ = ω k := by rw [hu, ht]; exact mul_one _
  have hdk : d k.val = (ω k : ℂ) := DFunLike.congr_fun hd k
  have hdt : d (σ t) = (((t : ℝ≥0) : ℝ) : ℂ) ^ z := hz t
  change (χ g : ℂ) * (((t : ℝ≥0) : ℝ) : ℂ) ^ z = d g
  rw [hχg, ← hdk, ← hdt, ← map_mul, hg]


/-- The logarithms of the residue cardinalities above one rational prime
are integral multiples of the logarithm of that rational residue cardinality. -/
private theorem sLocalOrbitalPrimary_log_norm (p : Vℚ) (v : V) (hv : v ∈ Sₚ(p)) :
    Real.log (v.asIdeal.absNorm : ℝ) =
      (v.asIdeal.inertiaDeg (𝓞 ℚ) : ℝ) * Real.log (p.asIdeal.absNorm : ℝ) := by
  have hvp := ((mem_sLocalPrimaryPlaces p v).mp hv).2
  let : v.asIdeal.IsPrime := v.isPrime
  let : v.asIdeal.LiesOver p.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hvp).symm⟩
  have hn := Ideal.absNorm_pow_inertiaDeg p.asIdeal v.asIdeal
  rw [← hn, Nat.cast_pow, Real.log_pow]


/-- The same uniformizer as the one used in the geometric Euler factor. -/
private def sLocalOrbitalUniformizer (v : S) : (v.val.adicCompletion F)ˣ :=
  let h := (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  Units.mk0 h.choose h.choose_spec.ne_zero

private theorem sLocalOrbitalUniformizer_norm (v : S) :
    uniformizerNorm(v, sLocalOrbitalUniformizer v) := by
  let h := (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  have hval : Valued.v (h.choose : v.val.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    h.choose_spec.trans (congrArg Units.val
      (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v.val.valuedAdicCompletion_surjective F)))
  change ‖(h.choose : v.val.adicCompletion F)‖ = _
  rw [FinitePlace.norm_def, hval, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
  simp

private def sLocalOrbitalInsert (v : S) : (v.val.adicCompletion F)ˣ → Jₛ :=
  fun x ↦ QuotientGroup.mk
    ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) (∀ w : S, w.val.adicCompletion F)).symm
      (1, (ContinuousMulEquiv.piUnits (M := fun w : S ↦ w.val.adicCompletion F)).symm
        (@Pi.mulSingle _ _ _ (Classical.decEq _) v x)))

private theorem sLocalOrbitalInsert_norm (v : S) (x : (v.val.adicCompletion F)ˣ) :
    ((mₛ (sLocalOrbitalInsert v x)).val : ℝ) = ‖x.val‖ := by
  have h := sLocalFiniteRestriction_norm (F := F) (S := S) v x
  change ((1 : PontryaginDual Jₛ) (sLocalOrbitalInsert v x) : ℂ) *
    (((mₛ (sLocalOrbitalInsert v x)).val : ℝ) : ℂ) ^ (1 : ℂ) = (‖x.val‖ : ℂ) at h
  simp only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] at h
  exact_mod_cast h

private def sLocalOrbitalUnitInsert (v : S) (u : (v.val.adicCompletionIntegers F)ˣ) : J₁ :=
  ⟨sLocalOrbitalInsert v (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u), by
    apply Units.ext
    apply NNReal.eq
    rw [sLocalOrbitalInsert_norm]
    exact Valued.toNormedField.norm_eq_one_iff.mpr
      ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
        (a := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u)).mp
        ⟨u.val.property, u.inv.property⟩)⟩

private def sLocalOrbitalUnramified (ω : PontryaginDual J₁) (v : S) : Prop :=
  ∀ u, ω (sLocalOrbitalUnitInsert v u) = 1

/-- At a place where the isotype is unramified, a pole occurs precisely when
the character is trivial on the inserted uniformizer. -/
private theorem sLocalOrbitalFinitePole_iff (ω : PontryaginDual J₁) (v : S) (c : Xₛ)
    (hc : onComponent(c, ω)) :
    v ∈ sLocalFinitePolePlaces c ↔ sLocalOrbitalUnramified ω v ∧
      c (sLocalOrbitalInsert v (sLocalOrbitalUniformizer v)) = 1 := by
  classical
  let ι := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom
  let ϖ := sLocalOrbitalUniformizer v
  have hu (z : ℂ) (u : (v.val.adicCompletionIntegers F)ˣ) :
      sLocalFiniteRestriction v (twistₛ c z) (ι u) = (ω (sLocalOrbitalUnitInsert v u) : ℂ) := by
    let i := sLocalOrbitalUnitInsert v u
    have hi := DFunLike.congr_fun hc i
    change c i.val = (ω i : ℂ) at hi
    change c i.val * (((mₛ i.val).val : ℝ) : ℂ) ^ z = (ω i : ℂ)
    rw [MonoidHom.mem_ker.mp i.property, Units.val_one, NNReal.coe_one,
      Complex.ofReal_one, Complex.one_cpow, mul_one, hi]
  have hunit (z : ℂ) : (∀ u, sLocalFiniteRestriction v (twistₛ c z) (ι u) = 1) ↔
      sLocalOrbitalUnramified ω v := by
    simp only [sLocalOrbitalUnramified, hu, ← Circle.coe_one, Circle.coe_inj]
  simp only [sLocalFinitePolePlaces, Finset.mem_filter, Finset.mem_univ, true_and]
  change meromorphicOrderAt (fun z ↦
    finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z))) 0 < 0 ↔ _
  by_cases hr : sLocalOrbitalUnramified ω v
  · let b := c (sLocalOrbitalInsert v ϖ)
    let q : ℝ := v.val.asIdeal.absNorm
    let A (z : ℂ) : ℂ := 1 - b * Complex.exp (-(Real.log q : ℂ) * z)
    have hq : 1 < q := by
      change (1 : ℝ) < (v.val.asIdeal.absNorm : ℝ)
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
    have hfun : (fun z ↦ finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z))) =
        fun z ↦ (A z)⁻¹ := by
      funext z
      rw [finiteLocalEulerFactor, ite_eq_left ((hunit z).2 hr)]
      change (1 - sLocalFiniteRestriction v (twistₛ c z) ϖ)⁻¹ = (A z)⁻¹
      rw [sLocalOrbitalPrincipalPart_range_le_ker_restrict, sLocalOrbitalUniformizer_norm]
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (inv_pos.mpr (zero_lt_one.trans hq)).ne'),
        ← Complex.ofReal_log (inv_pos.mpr (zero_lt_one.trans hq)).le, Real.log_inv, Complex.ofReal_neg]
      rfl
    have hA : AnalyticAt ℂ A 0 := by dsimp only [A]; fun_prop
    rw [hfun]
    change meromorphicOrderAt (fun z ↦ (A z)⁻¹) 0 < 0 ↔ _ ∧ b = 1
    by_cases hb : b = 1
    · have hd : HasDerivAt A (Real.log q : ℂ) 0 := by
        have hexp := ((hasDerivAt_id (0 : ℂ)).const_mul (-(Real.log q : ℂ))).cexp
        simpa [A, b, hb] using hexp.const_sub (1 : ℂ)
      have hord : analyticOrderAt A 0 = (1 : ℕ∞) := by
        apply (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hA (n := 1)).mpr
        refine ⟨fun k hk ↦ ?_, ?_⟩
        · have : k = 0 := by omega
          simp [this, A, hb]
        · simpa [iteratedDeriv_one, hd.deriv] using (Real.log_pos hq).ne'
      have hm : meromorphicOrderAt A 0 = 1 := by
        simpa [hord] using hA.meromorphicOrderAt_eq
      change meromorphicOrderAt A⁻¹ 0 < 0 ↔ _ ∧ b = 1
      rw [meromorphicOrderAt_inv, hm]
      simp only [hr, hb, and_self, iff_true]
      change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
      exact WithTop.coe_lt_coe.mpr (by decide)
    · have hA0 : A 0 ≠ 0 := by
        change 1 - b * Complex.exp (-(Real.log q : ℂ) * 0) ≠ 0
        rw [mul_zero, Complex.exp_zero, mul_one, sub_ne_zero]
        exact Ne.symm hb
      have hnonneg := (hA.inv hA0).meromorphicOrderAt_nonneg
      exact iff_of_false (not_lt_of_ge hnonneg) (fun h ↦ hb h.2)
  · have hfun : (fun z ↦ finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z))) =
        fun _ ↦ (1 : ℂ) := by
      funext z
      rw [finiteLocalEulerFactor, ite_eq_right (fun h ↦ hr ((hunit z).1 h))]
    rw [hfun]
    simp [hr, not_lt_of_ge analyticAt_const.meromorphicOrderAt_nonneg]

/-- a local uniformizer has norm equal to the reciprocal residue cardinality. -/
private theorem sLocalOrbitalIndex_enumerable_or_empty_uniformizer
    {F : Type*} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (v : S) :
    ∃ u : (v.val.adicCompletion F)ˣ,
      ‖(u : v.val.adicCompletion F)‖ = ((v.val.asIdeal.absNorm : ℝ)⁻¹) := by
  let hπ := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  refine ⟨Units.mk0 hπ.choose hπ.choose_spec.ne_zero, ?_⟩
  have hval : Valued.v (hπ.choose : v.val.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    hπ.choose_spec.trans (congrArg Units.val
      (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v.val.valuedAdicCompletion_surjective F)))
  change ‖(hπ.choose : v.val.adicCompletion F)‖ = _
  rw [FinitePlace.norm_def, hval, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
  simp

/-- Paper: Theorem 7.3.1.6(2), p. 345.
Primary pole centers on one norm component form a countable set. -/
private theorem sLocalOrbitalIndex_enumerable_or_empty_countable_centers
    {F : Type*} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (p : (HeightOneSpectrum (𝓞 ℚ))) (ω : PontryaginDual (((sIdeleQuotientNorm F S)).ker)) :
    Countable {c : (QuasiCharacter (SIdeleQuotient F S)) // (normOneRestriction (sIdeleQuotientNorm F S) c = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω) ∧
      0 < sLocalFinitePoleMultiplicity ((sLocalPrimaryPlaces S p)) c} := by
  classical
  obtain ⟨χ, hcomp, hcover⟩ := sLocalOrbitalIndex_enumerable_or_empty_chart ω
  choose u hu using (sLocalOrbitalIndex_enumerable_or_empty_uniformizer (F := F) (S := S))
  have phases := fun v : S ↦ (existsUnique_sLocalOrbitalPhase χ v (u v) (hu v)).exists
  choose t ht using phases
  let lattice : S × ℤ → (QuasiCharacter (SIdeleQuotient F S)) := fun j ↦ ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ))
    (((j.2 : ℝ) * (2 * Real.pi / Real.log (j.1.val.asIdeal.absNorm : ℝ)) - t j.1 : ℝ) * Complex.I)
  have hsub : {c : (QuasiCharacter (SIdeleQuotient F S)) | (normOneRestriction (sIdeleQuotientNorm F S) c = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω) ∧
      0 < sLocalFinitePoleMultiplicity ((sLocalPrimaryPlaces S p)) c} ⊆ Set.range lattice := by
    intro c hc
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hc.2
    obtain ⟨s, hs⟩ := hcover c hc.1
    obtain ⟨n, hn⟩ := (existsUnique_sLocalOrbitalLatticeIndex χ v (u v) (hu v)
      (t v) (ht v) c ⟨s, hs.symm⟩ (Finset.mem_filter.mp hv).1).exists
    exact ⟨(v, n), hn.symm⟩
  exact ((Set.countable_range lattice).mono hsub).to_subtype

/-- integer imaginary twists of the local period preserve the Euler factor. -/
private theorem sLocalOrbitalIndex_enumerable_or_empty_periodic
    {F : Type*} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (v : S) (c : (QuasiCharacter (SIdeleQuotient F S))) (n : ℕ) :
    finiteLocalEulerFactor v.val (sLocalFiniteRestriction v
      ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) c (((n : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) : ℝ) * Complex.I))) =
      finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c) := by
  classical
  let a : ℂ := ((n : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) : ℝ) * Complex.I
  let ι := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom
  have hunit (u : (v.val.adicCompletionIntegers F)ˣ) :
      sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) c a) (ι u) = sLocalFiniteRestriction v c (ι u) := by
    rw [sLocalOrbitalPrincipalPart_range_le_ker_restrict]
    have hu : ‖((ι u : (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F)‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
          (a := ι u)).mp ⟨u.val.property, u.inv.property⟩)
    rw [hu, Complex.ofReal_one, Complex.one_cpow, mul_one]
  have key : (∀ u, sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) c a) (ι u) = 1) ↔
      (∀ u, sLocalFiniteRestriction v c (ι u) = 1) := forall_congr' fun u ↦ by rw [hunit u]
  let hπ := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.val.adicCompletion F)ˣ := Units.mk0 hπ.choose hπ.choose_spec.ne_zero
  have hπ_norm : ‖(π : v.val.adicCompletion F)‖ = ((v.val.asIdeal.absNorm : ℝ)⁻¹) := by
    have hval : Valued.v (π : v.val.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
      hπ.choose_spec.trans (congrArg Units.val
        (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
          (v.val.valuedAdicCompletion_surjective F)))
    rw [FinitePlace.norm_def, hval, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    simp
  have hq : (1 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have hlog : Real.log (v.val.asIdeal.absNorm : ℝ) ≠ 0 := (Real.log_pos hq).ne'
  have hpow : (((‖(π : v.val.adicCompletion F)‖ : ℝ) : ℂ)) ^ a = 1 := by
    rw [hπ_norm, Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero (zero_lt_one.trans hq).ne')),
      ← Complex.ofReal_log (inv_pos.mpr (zero_lt_one.trans hq)).le, Real.log_inv]
    have he : (↑(-Real.log (v.val.asIdeal.absNorm : ℝ)) : ℂ) * a =
        ((-(n : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      dsimp [a]
      simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_ofNat, Complex.ofReal_natCast, Int.cast_neg, Int.cast_natCast]
      calc
        _ = -(n : ℂ) * (2 * Real.pi * Complex.I) *
            ((Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) /
              (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)) := by ring
        _ = _ := by rw [div_self (Complex.ofReal_ne_zero.mpr hlog), mul_one]
    rw [he]
    exact Complex.exp_int_mul_two_pi_mul_I (-(n : ℤ))
  have hval : sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) c a) π = sLocalFiniteRestriction v c π := by
    rw [sLocalOrbitalPrincipalPart_range_le_ker_restrict, hpow, mul_one]
  change (if ∀ u, sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) c a) (ι u) = 1 then
      (1 - sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) c a) π)⁻¹ else 1) =
    (if ∀ u, sLocalFiniteRestriction v c (ι u) = 1 then
      (1 - sLocalFiniteRestriction v c π)⁻¹ else 1)
  rw [key, hval]

/-- Paper: Theorem 7.3.1.6(2), p. 345.
Every primary pole has infinitely many distinct primary poles on the same component,
obtained by imaginary twists preserving one contributing finite place. -/
private theorem sLocalOrbitalIndex_enumerable_or_empty_infinite_centers
    {F : Type*} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (p : (HeightOneSpectrum (𝓞 ℚ))) (ω : PontryaginDual (((sIdeleQuotientNorm F S)).ker)) (c : (QuasiCharacter (SIdeleQuotient F S)))
    (hc : (normOneRestriction (sIdeleQuotientNorm F S) c = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω) ∧ 0 < sLocalFinitePoleMultiplicity ((sLocalPrimaryPlaces S p)) c) :
    ∃ f : ℕ → {d : (QuasiCharacter (SIdeleQuotient F S)) // (normOneRestriction (sIdeleQuotientNorm F S) d = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω) ∧
      0 < sLocalFinitePoleMultiplicity ((sLocalPrimaryPlaces S p)) d}, Function.Injective f := by
  classical
  obtain ⟨χ, hcomp, hcover⟩ := sLocalOrbitalIndex_enumerable_or_empty_chart ω
  obtain ⟨a, rfl⟩ := hcover c hc.1
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hc.2
  obtain ⟨hv, hvp⟩ := Finset.mem_filter.mp hv
  let per : ℝ := 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)
  let z (n : ℕ) : ℂ := ((n : ℝ) * per : ℝ) * Complex.I
  have hpos (n : ℕ) : 0 < sLocalFinitePoleMultiplicity ((sLocalPrimaryPlaces S p)) (((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) (z n + a)) := by
    apply Finset.card_pos.mpr
    refine ⟨v, Finset.mem_filter.mpr ⟨?_, hvp⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have he : (fun w : ℂ ↦ finiteLocalEulerFactor v.val
        (sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) (((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) (z n + a)) w))) =
      (fun w : ℂ ↦ finiteLocalEulerFactor v.val
        (sLocalFiniteRestriction v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) (((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) a) w))) := by
      funext w
      have h := sLocalOrbitalIndex_enumerable_or_empty_periodic v ((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) (((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) a) w) n
      simpa only [normTwist_normTwist, add_assoc, add_left_comm, add_comm] using h
    rw [he]
    exact (Finset.mem_filter.mp hv).2
  have hinj : Injective (((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ))) := by
    intro s t he
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
    let P := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 s
    have hs (u : ℝ≥0ˣ) : P u = ((u.val : ℝ) : ℂ) ^ s := one_mul _
    apply (existsUnique_complexPower P).unique hs
    intro u
    have h := DFunLike.congr_fun he (σ u)
    change (χ (σ u) : ℂ) * ((((sIdeleQuotientNorm F S) (σ u) : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ (σ u) : ℂ) * ((((sIdeleQuotientNorm F S) (σ u) : ℝ≥0) : ℝ) : ℂ) ^ t at h
    rw [hσ u] at h
    exact (hs u).trans (mul_left_cancel₀ (Circle.coe_ne_zero _) h)
  refine ⟨fun n ↦ ⟨((quasiCharacterNormTwist (G := (SIdeleQuotient F S)) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous) ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)) (z n + a), hcomp _, hpos n⟩, ?_⟩
  intro n m h
  have he := congrArg Complex.im (add_right_cancel (hinj (congrArg Subtype.val h)))
  have hper : per ≠ 0 := by
    have hq : (1 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
    exact (div_pos (by positivity) (Real.log_pos hq)).ne'
  have he' : (n : ℝ) * per = (m : ℝ) * per := by
    simpa only [z, Complex.mul_I_im, Complex.ofReal_re] using he
  exact Nat.cast_injective (mul_right_cancel₀ hper he')

/-- Paper: Theorem 7.3.1.6(2), p. 345.
The common index set either admits an enumeration by the natural numbers or is
empty and the corresponding primary quotient is zero. -/
theorem sLocalOrbitalIndex_enumerable_or_empty
    (p : Vℚ) (ω : PontryaginDual J₁)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) :
    Nonempty (ℕ ≃ Idx(p, ω)) ∨ (IsEmpty (Idx(p, ω)) ∧ Subsingleton (Q(p, ω))) := by
  classical
  by_cases h : Nonempty (Idx(p, ω))
  · have : Countable {c : Xₛ // onComponent(c, ω) ∧
        0 < sLocalFinitePoleMultiplicity (Sₚ(p)) c} :=
      sLocalOrbitalIndex_enumerable_or_empty_countable_centers p ω
    let centerOffset (j : Idx(p, ω)) :
        {c : Xₛ // onComponent(c, ω) ∧
          0 < sLocalFinitePoleMultiplicity (Sₚ(p)) c} × ℕ :=
      (⟨j.val.1, j.property.1, lt_of_le_of_lt (Nat.zero_le _) j.property.2⟩, j.val.2)
    have : Countable (Idx(p, ω)) := (show Function.Injective centerOffset from by
      intro a b hab
      apply Subtype.ext
      exact Prod.ext (congrArg (fun x ↦ x.1.val) hab)
        (congrArg (fun x :
          {c : Xₛ // onComponent(c, ω) ∧
            0 < sLocalFinitePoleMultiplicity (Sₚ(p)) c} × ℕ ↦ x.2) hab)).countable
    obtain ⟨j⟩ := h
    obtain ⟨f, hf⟩ := sLocalOrbitalIndex_enumerable_or_empty_infinite_centers
      p ω j.val.1 ⟨j.property.1, lt_of_le_of_lt (Nat.zero_le _) j.property.2⟩
    have : Infinite (Idx(p, ω)) := Infinite.of_injective
      (fun n : ℕ ↦ (⟨((f n).val, 0), (f n).property.1, (f n).property.2⟩ : Idx(p, ω)))
      (by
        intro a b hab
        apply hf
        apply Subtype.ext
        exact congrArg (fun j : Idx(p, ω) ↦ j.val.1) hab)
    exact Or.inl nonempty_equiv_of_countable
  · right
    have hEmpty : IsEmpty (Idx(p, ω)) := ⟨fun j ↦ h ⟨j⟩⟩
    refine ⟨hEmpty, ⟨?_⟩⟩
    intro x y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (Rₚ(p, ω)) x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (Rₚ(p, ω)) y
    have hzero (z : Θₛ(ω)) : π(p, ω) z = 0 := (Submodule.Quotient.mk_eq_zero _).2
      ((sLocalOrbitalFourierJet_commonKer p ω _hS _hp _hPic z).2 (fun j ↦ isEmptyElim j))
    exact (hzero x).trans (hzero y).symm


/-- A selected Euler pole lies at a unitary character. -/
private theorem sLocalOrbitalIndex_isUnitary (p : Vℚ) (ω : PontryaginDual J₁)
    (j : Idx(p, ω)) : ∃ ξ : PontryaginDual Jₛ, j.val.1 = (circleToComplex).comp ξ := by
  classical
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) j.property.2)
  obtain ⟨χ, s, hs⟩ := sLocalOrbitalIndex_enumerable_or_empty_chart ω
  let u := sLocalOrbitalUniformizer v
  obtain ⟨t, ht, _⟩ := existsUnique_sLocalOrbitalPhase χ v u (sLocalOrbitalUniformizer_norm v)
  obtain ⟨n, hn, _⟩ := existsUnique_sLocalOrbitalLatticeIndex χ v u
    (sLocalOrbitalUniformizer_norm v) t ht j.val.1
    (by obtain ⟨a, ha⟩ := hs _ j.property.1; exact ⟨a, ha.symm⟩)
    (Finset.mem_filter.mp hv).1
  have hnorm (g : Jₛ) : ‖j.val.1 g‖ = 1 := by
    rw [hn]
    change ‖(χ g : ℂ) * (((mₛ g).val : ℝ) : ℂ) ^
      (((((n : ℝ) * period(v) - t) : ℝ) : ℂ) * Complex.I)‖ = 1
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos
      (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.rpow_zero]
  let ξ : PontryaginDual Jₛ :=
    { toFun := fun g ↦ ⟨j.val.1 g, mem_sphere_zero_iff_norm.mpr (hnorm g)⟩
      map_one' := Subtype.ext (map_one j.val.1)
      map_mul' := fun g h ↦ Subtype.ext (map_mul j.val.1 g h)
      continuous_toFun := j.val.1.continuous.subtype_mk _ }
  exact ⟨ξ, ContinuousMonoidHom.ext fun _ ↦ rfl⟩

private def sLocalOrbitalActivePlaces (p : Vℚ) (ω : PontryaginDual J₁) : Finset S :=
  open Classical in
  Finset.univ.filter fun v : S ↦ v.val ∈ Sₚ(p) ∧ sLocalOrbitalUnramified ω v

private def sLocalOrbitalActiveEquiv (p : Vℚ) (ω : PontryaginDual J₁) :=
  (Fintype.equivFin (sLocalOrbitalActivePlaces p ω)).symm

private def sLocalOrbitalDifferenceGenerator (p : Vℚ) (ω : PontryaginDual J₁)
    (i : Fin (Fintype.card (sLocalOrbitalActivePlaces p ω))) : Jₛ :=
  let v := (sLocalOrbitalActiveEquiv p ω i).val
  (sLocalOrbitalInsert v (sLocalOrbitalUniformizer v))⁻¹

private theorem sLocalOrbitalDifferenceGenerator_norm (p : Vℚ) (ω : PontryaginDual J₁)
    (i : Fin (Fintype.card (sLocalOrbitalActivePlaces p ω))) :
    ((mₛ (sLocalOrbitalDifferenceGenerator p ω i)).val : ℝ) =
      ((sLocalOrbitalActiveEquiv p ω i).val.val.asIdeal.absNorm : ℝ) := by
  let v := (sLocalOrbitalActiveEquiv p ω i).val
  change ((mₛ (sLocalOrbitalInsert v (sLocalOrbitalUniformizer v))⁻¹).val : ℝ) = _
  rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, sLocalOrbitalInsert_norm,
    sLocalOrbitalUniformizer_norm, inv_inv]


open MeasureTheory

private local instance sLocalOrbitalQuotient_t2 : T2Space Jₛ := by
  let := isClosed_sProjectedDiagonal (F := F) (S := S)
  infer_instance

private local instance sLocalOrbitalQuotient_locallyCompact : LocallyCompactSpace Jₛ := by
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  infer_instance

private local instance sLocalOrbitalQuotient_secondCountable : SecondCountableTopology Jₛ := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (SAdeleRing F S) := inferInstanceAs
    (SecondCountableTopology (((w : InfinitePlace F) → w.Completion) ×
      ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology (SAdeleRing F S)ˣ :=
    (sIdeleGroup_description F S).1.secondCountableTopology
  infer_instance

local notation "mGroup" => (⟨mₛ, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ : Jₛ →ₜ* ℝ≥0ˣ)
local notation "ModelIndex(" p "," ω ")" =>
  {k : PontryaginDual Jₛ × ℕ // k.2 < modulatedPeriodicMultiplicity mGroup ω⁻¹
    (sLocalOrbitalDifferenceGenerator p ω) k.1}

private theorem sLocalOrbitalDifferenceGenerator_multiplicity
    (p : Vℚ) (ω : PontryaginDual J₁) (ξ : PontryaginDual Jₛ)
    (hξ : ∀ u : J₁, ξ u.val = ω⁻¹ u) :
    modulatedPeriodicMultiplicity mGroup ω⁻¹ (sLocalOrbitalDifferenceGenerator p ω) ξ =
      sLocalFinitePoleMultiplicity (Sₚ(p)) ((circleToComplex).comp ξ⁻¹) := by
  classical
  let c := (circleToComplex).comp ξ⁻¹
  have hc : onComponent(c, ω) := by
    ext u
    change ((ξ⁻¹ u.val : Circle) : ℂ) = (ω u : ℂ)
    have he : ξ⁻¹ u.val = ω u := by
      change (ξ u.val)⁻¹ = ω u
      rw [hξ]
      exact inv_inv (ω u)
    exact congrArg Subtype.val he
  unfold modulatedPeriodicMultiplicity sLocalFinitePoleMultiplicity
  apply Finset.card_bij (fun i _ ↦ (sLocalOrbitalActiveEquiv p ω i).val)
  · intro i hi
    have hlocal := ((Finset.mem_filter.mp hi).2)
    have hgen := ((mem_modulatedCyclicAnnihilatorFiber_iff _ _ _ _).mp hlocal).1
    let v := sLocalOrbitalActiveEquiv p ω i
    obtain ⟨hv, hu⟩ := (Finset.mem_filter.mp v.property).2
    refine Finset.mem_filter.mpr ⟨(sLocalOrbitalFinitePole_iff ω v.val c hc).2 ⟨hu, ?_⟩, hv⟩
    change (((ξ (sLocalOrbitalInsert v.val (sLocalOrbitalUniformizer v.val)))⁻¹ : Circle) : ℂ) = 1
    change ξ (sLocalOrbitalInsert v.val (sLocalOrbitalUniformizer v.val))⁻¹ = 1 at hgen
    rw [map_inv] at hgen
    exact congrArg Subtype.val hgen
  · intro i _ j _ h
    exact (sLocalOrbitalActiveEquiv p ω).injective (Subtype.ext h)
  · intro v hv
    obtain ⟨hpole, hp⟩ := Finset.mem_filter.mp hv
    obtain ⟨hu, hvan⟩ := (sLocalOrbitalFinitePole_iff ω v c hc).mp hpole
    let a : sLocalOrbitalActivePlaces p ω := ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp, hu⟩⟩
    let i := (sLocalOrbitalActiveEquiv p ω).symm a
    have hi : sLocalOrbitalActiveEquiv p ω i = a := (sLocalOrbitalActiveEquiv p ω).apply_symm_apply a
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, congrArg Subtype.val hi⟩
    apply (mem_modulatedCyclicAnnihilatorFiber_iff _ _ _ _).mpr
    refine ⟨?_, hξ⟩
    change ξ (sLocalOrbitalInsert (sLocalOrbitalActiveEquiv p ω i).val
      (sLocalOrbitalUniformizer (sLocalOrbitalActiveEquiv p ω i).val))⁻¹ = 1
    rw [hi]
    apply Circle.ext
    rw [map_inv]
    exact hvan

private theorem sLocalOrbitalModelIndex_restrict (p : Vℚ) (ω : PontryaginDual J₁)
    (j : ModelIndex(p, ω)) : ∀ u : J₁, j.val.1 u.val = ω⁻¹ u := by
    classical
    have hpos := lt_of_le_of_lt (Nat.zero_le _) j.property
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ((mem_modulatedCyclicAnnihilatorFiber_iff _ _ _ _).mp
      (Finset.mem_filter.mp hi).2).2

private theorem sLocalOrbitalModelIndex_equiv (p : Vℚ) (ω : PontryaginDual J₁) :
    ∃ e : ModelIndex(p, ω) ≃ Idx(p, ω), ∀ j,
      (e j).val = (((circleToComplex).comp j.val.1⁻¹), j.val.2) := by
  classical
  let J := ModelIndex(p, ω)
  have hrestrict (j : J) := sLocalOrbitalModelIndex_restrict p ω j
  let f (j : J) : Idx(p, ω) :=
    ⟨(((circleToComplex).comp j.val.1⁻¹), j.val.2), by
      constructor
      · ext u
        change ((j.val.1⁻¹ u.val : Circle) : ℂ) = (ω u : ℂ)
        have he : j.val.1⁻¹ u.val = ω u := by
          change (j.val.1 u.val)⁻¹ = ω u
          rw [hrestrict j]
          exact inv_inv (ω u)
        exact congrArg Subtype.val he
      · rw [← sLocalOrbitalDifferenceGenerator_multiplicity p ω j.val.1 (hrestrict j)]
        exact j.property⟩
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, fun j ↦ rfl⟩
  · intro u v h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    change (((circleToComplex).comp u.val.1⁻¹), u.val.2) =
      (((circleToComplex).comp v.val.1⁻¹), v.val.2) at h'
    refine Prod.ext ?_ (congrArg (fun z : Xₛ × ℕ ↦ z.2) h')
    apply inv_injective
    ext g
    exact congrArg (fun z : Xₛ × ℕ ↦ z.1 g) h'
  · intro j
    obtain ⟨ξ, hξ⟩ := sLocalOrbitalIndex_isUnitary p ω j
    have hrest : ∀ u : J₁, ξ⁻¹ u.val = ω⁻¹ u := by
      intro u
      have hc := DFunLike.congr_fun j.property.1 u
      change j.val.1 u.val = (ω u : ℂ) at hc
      rw [hξ] at hc
      change (ξ u.val : ℂ) = (ω u : ℂ) at hc
      change (ξ u.val)⁻¹ = (ω u)⁻¹
      exact congrArg Inv.inv (Circle.ext hc)
    have hidx : j.val.2 < modulatedPeriodicMultiplicity mGroup ω⁻¹
        (sLocalOrbitalDifferenceGenerator p ω) ξ⁻¹ := by
      rw [sLocalOrbitalDifferenceGenerator_multiplicity p ω _ hrest]
      have hh : (circleToComplex).comp (ξ⁻¹)⁻¹ = j.val.1 :=
        (congrArg (fun ψ : PontryaginDual Jₛ ↦ (circleToComplex).comp ψ) (inv_inv ξ)).trans hξ.symm
      exact hh.symm ▸ j.property.2
    refine ⟨⟨(ξ⁻¹, j.val.2), hidx⟩, Subtype.ext (Prod.ext ?_ rfl)⟩
    change (circleToComplex).comp (ξ⁻¹)⁻¹ = j.val.1
    exact (congrArg (fun ψ : PontryaginDual Jₛ ↦ (circleToComplex).comp ψ) (inv_inv ξ)).trans hξ.symm


private theorem sLocalOrbital_modulation :
    IsModulation (mGroup) ∧ Surjective (mGroup) := by
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  have hs : Surjective (mGroup) := hτ.surjective
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  obtain ⟨g, hg⟩ := hs t
  exact ⟨⟨isProperMap_sIdeleQuotientNorm F S, g, hg.trans_ne ht⟩, hs⟩

local notation "I₋" => Ioi (-1 : ℝ)
local notation "hI₋" => (show (0 : ℝ) ∈ I₋ by norm_num)
local notation "H₋(" ω ")" => ↥(modulatedDecayIsotype mGroup I₋ hI₋ ω)

private theorem sLocalOrbital_isotype_eq (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (ω : PontryaginDual J₁) :
    modulatedDecayIsotype mGroup I h0 ω = sLocalDecayIsotype I ω := by
  ext f
  exact (mem_modulatedDecayIsotype_iff mGroup ω I h0 f).trans
    (mem_sLocalDecayIsotype I ω f).symm

private theorem sLocalOrbital_modulationShift :
    ∃ W : ModulatedExponentialDecay mGroup (Ioi (0 : ℝ)) →L[ℂ]
        ModulatedExponentialDecay mGroup I₋,
      ∀ f g, (W f).val g = (((mₛ g).val : ℝ) : ℂ) * f.val g := by
  have he : ((fun b : ℝ ↦ b - 1) '' Ioi (0 : ℝ)) = I₋ := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      change -1 < b - 1
      linarith [show 0 < b from hb]
    · intro ha
      exact ⟨a + 1, by change 0 < a + 1; linarith [show -1 < a from ha], add_sub_cancel_right ..⟩
  have h := modulatedExponentialDecay_shift_equiv mGroup (Ioi (0 : ℝ))
    sLocalOrbital_modulation.1 sLocalOrbital_modulation.2 ordConnected_Ioi ⟨1, one_pos⟩ 1
  rw [he] at h
  obtain ⟨W, hW⟩ := h
  refine ⟨W.toContinuousLinearMap, fun f g ↦ ?_⟩
  have hx := congrFun (hW f) g
  change (W f).val g =
    ((Real.rpow ((mₛ g).val : ℝ) 1 : ℝ) : ℂ) * f.val g at hx
  change (W f).val g = (((mₛ g).val : ℝ) : ℂ) * f.val g
  exact hx.trans (congrArg (fun a : ℝ ↦ (a : ℂ) * f.val g) (Real.rpow_one _))

private def sLocalOrbital_pairPredicate (ω η : PontryaginDual J₁) : Prop :=
    ∃ U : Θₛ(ω) →L[ℂ] ↥(sLocalDecayIsotype (Ioi (0 : ℝ)) ω) ×
        ↥(sLocalDecayIsotype (Ioi (0 : ℝ)) η), ∀ f : ℬₛ,
        (U ((Kₛ(ω)).mkQ f)).1.val.val = ⇑(sLocalHomogeneousAdelicThetaLinearMap F S ω f) ∧
        (U ((Kₛ(ω)).mkQ f)).2.val.val =
          ⇑(sLocalHomogeneousAdelicThetaLinearMap F S η (sAdeleSchwartzFourier f))

local notation "ιCech" => (⟨(mₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ)
private theorem sLocalOrbital_pair_lifted (χ : PontryaginDual Jₛ) :
    sLocalOrbital_pairPredicate (F := F) (S := S) (χ.comp ιCech) ((χ⁻¹).comp ιCech) :=
  (existsUnique_sLocalCechThetaPair (F := F) (S := S) χ).exists

private theorem sLocalOrbital_cechPair (ω : PontryaginDual J₁) :
    sLocalOrbital_pairPredicate (F := F) (S := S) ω ω⁻¹ := by
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨χ, hχ, _⟩ := (existsUnique_sLocalNormSectionCharacter (F := F) (S := S) τ hτ ω).exists
  have e : χ.comp ιCech = ω := hχ
  have ei : (χ⁻¹).comp ιCech = ω⁻¹ := ContinuousMonoidHom.ext fun u ↦ congrArg Inv.inv (DFunLike.congr_fun e u)
  exact (congrArg₂ (sLocalOrbital_pairPredicate (F := F) (S := S)) e ei).mp (sLocalOrbital_pair_lifted χ)

private theorem sLocalOrbital_normTranslate (k : J₁) (g : Jₛ) :
    mₛ (k.val⁻¹ * g) = mₛ g := by
  calc
    _ = (mₛ k.val)⁻¹ * mₛ g := (map_mul mₛ k.val⁻¹ g).trans (congrArg (· * mₛ g) (map_inv mₛ k.val))
    _ = _ := by rw [MonoidHom.mem_ker.mp k.property, inv_one, one_mul]

private theorem sLocalOrbital_shiftIsotype (η : PontryaginDual J₁) :
    ∃ T : ↥(sLocalDecayIsotype (Ioi (0 : ℝ)) η) →L[ℂ] H₋(η),
      ∀ v g, (T v).val.val g = (((mₛ g).val : ℝ) : ℂ) * v.val.val g := by
  obtain ⟨W, hW⟩ := sLocalOrbital_modulationShift (F := F) (S := S)
  let T := W.comp (sLocalDecayIsotype (Ioi (0 : ℝ)) η).subtypeL
  have hm (v : sLocalDecayIsotype (Ioi (0 : ℝ)) η) :
      T v ∈ modulatedDecayIsotype mGroup I₋ hI₋ η := by
    apply (mem_modulatedDecayIsotype_iff mGroup η I₋ hI₋ (T v)).mpr
    intro k g
    have hv := (mem_sLocalDecayIsotype (Ioi (0 : ℝ)) η v.val).mp v.property k g
    change (W v.val).val (k.val⁻¹ * g) = (η k : ℂ) * (W v.val).val g
    calc
      _ = _ := hW v.val (k.val⁻¹ * g)
      _ = (η k : ℂ) * ((((mₛ g).val : ℝ) : ℂ) * v.val.val g) := by
        rw [sLocalOrbital_normTranslate k g, hv, mul_left_comm]
      _ = _ := congrArg ((η k : ℂ) * ·) (hW v.val g).symm
  exact ⟨T.codRestrict _ hm, fun v g ↦ hW v.val g⟩

/-- The Fourier component of the Čech map, multiplied by the idelic norm. -/
private theorem sLocalOrbital_shiftedFourier (ω : PontryaginDual J₁) :
    ∃ A : Θₛ(ω) →L[ℂ] H₋(ω⁻¹), ∀ (f : ℬₛ) (g : Jₛ),
      (A ((Kₛ(ω)).mkQ f)).val.val g = (((mₛ g).val : ℝ) : ℂ) *
        sLocalHomogeneousAdelicThetaLinearMap F S ω⁻¹ (sAdeleSchwartzFourier f) g := by
  let U := (sLocalOrbital_cechPair (F := F) (S := S) ω).choose
  let T := (sLocalOrbital_shiftIsotype (F := F) (S := S) ω⁻¹).choose
  have hU := (sLocalOrbital_cechPair (F := F) (S := S) ω).choose_spec
  have hT := (sLocalOrbital_shiftIsotype (F := F) (S := S) ω⁻¹).choose_spec
  refine ⟨T.comp ((ContinuousLinearMap.snd ℂ _ _).comp U), fun f g ↦ ?_⟩
  exact (hT _ g).trans (congrArg (fun v : ℂ ↦ (((mₛ g).val : ℝ) : ℂ) * v) (congrFun (hU f).2 g))

local notation "H₀(" ω ")" =>
  ↥(modulatedDecayIsotype mGroup (univ : Set ℝ) (mem_univ (0 : ℝ)) ω)

private theorem sLocalOrbital_restrict_range {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (H : Submodule ℂ E) (D : E →L[ℂ] E) (hD : ∀ x ∈ H, D x ∈ H) :
    (H.map D.toLinearMap).comap H.subtype = (D.restrict hD).range := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩
  · rintro ⟨y, he⟩
    exact ⟨y.val, y.property, congrArg Subtype.val he⟩

private theorem sLocalOrbital_intervalQuotient_gen {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (ω : PontryaginDual m.ker) (L : List G) (hL : L ≠ [])
    (hgen : ∀ g ∈ L, 1 < (m g).val) :
    let R₀ := (modulatedIsotypicDifferenceProduct m hm
      hms ω univ ordConnected_univ (mem_univ (0 : ℝ)) L).range
    let Rint := (modulatedIsotypicDifferenceProduct m hm
      hms ω I₋ ordConnected_Ioi hI₋ L).range
    ∃ T : (↥(modulatedDecayIsotype m (univ : Set ℝ) (mem_univ (0 : ℝ)) ω) ⧸ R₀) ≃L[ℂ] (↥(modulatedDecayIsotype m I₋ hI₋ ω) ⧸ Rint),
      ∀ f : ↥(modulatedDecayIsotype m (univ : Set ℝ) (mem_univ (0 : ℝ)) ω), ∃ g : ↥(modulatedDecayIsotype m I₋ hI₋ ω),
        (∀ x : G, g.val.val x = f.val.val x) ∧ T (R₀.mkQ f) = Rint.mkQ g := by
  intro R₀ Rint
  have h :=
    modulatedIsotypicDifferenceProduct_quotient_equivs m hm
      hms ω L hL hgen I₋ isOpen_Ioi ordConnected_Ioi hI₋
  dsimp only at h
  rw [sLocalOrbital_restrict_range _ _
    (modulatedDifferenceProduct_mem_isotype m hm
      hms ω univ ordConnected_univ (mem_univ (0 : ℝ)) L),
    sLocalOrbital_restrict_range _ _
      (modulatedDifferenceProduct_mem_isotype m hm
        hms ω I₋ ordConnected_Ioi hI₋ L)] at h
  exact h.elim fun T hT ↦ ⟨T, hT.choose_spec.1⟩





private theorem sLocalOrbital_intervalQuotient
    (ω : PontryaginDual J₁) (L : List Jₛ) (hL : L ≠ [])
    (hgen : ∀ g ∈ L, 1 < (mGroup g).val) :
    let R₀ := (modulatedIsotypicDifferenceProduct mGroup sLocalOrbital_modulation.1
      sLocalOrbital_modulation.2 ω univ ordConnected_univ (mem_univ (0 : ℝ)) L).range
    let Rint := (modulatedIsotypicDifferenceProduct mGroup sLocalOrbital_modulation.1
      sLocalOrbital_modulation.2 ω I₋ ordConnected_Ioi hI₋ L).range
    ∃ T : (H₀(ω) ⧸ R₀) ≃L[ℂ] (H₋(ω) ⧸ Rint),
      ∀ f : H₀(ω), ∃ g : H₋(ω),
        (∀ x : Jₛ, g.val.val x = f.val.val x) ∧ T (R₀.mkQ f) = Rint.mkQ g := by
  exact sLocalOrbital_intervalQuotient_gen mGroup sLocalOrbital_modulation.1 sLocalOrbital_modulation.2 ω L hL hgen


attribute [local instance] instMeasurableSpaceSIdeleQuotient

private local instance sLocalOrbitalQuotient_borel : BorelSpace Jₛ := ⟨rfl⟩

local notation "μorb" => sLocalQuotientTamagawaMeasure F S

private local instance sLocalOrbitalQuotient_haar : MeasureTheory.Measure.IsHaarMeasure (μorb) :=
  (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1

section
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A polynomial times an exponential on the half disk is controlled by a slightly larger
real exponential. The constant is independent of the integration variable. -/
private theorem primaryExpMoment_bound (n : ℕ) (z : ℂ) (hz : ‖z‖ < 1/4) (t : ℝ) :
    |t| ^ n * Real.exp (z.re * t) ≤ ((n.factorial : ℝ) * 4 ^ n) * Real.exp (|t|/2) := by
  have hpow := Real.pow_div_factorial_le_exp _ (show 0 ≤ |t| / 4 by positivity) n
  have hpoly : |t| ^ n ≤ ((n.factorial : ℝ) * 4 ^ n) * Real.exp (|t| / 4) := by
    rw [div_pow] at hpow
    field_simp at hpow
    nlinarith only [hpow]
  have hz' : z.re * t ≤ |t|/4 := calc
    _ ≤ |z.re| * |t| := (le_abs_self _).trans_eq (abs_mul _ _)
    _ ≤ (1/4) * |t| := mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans hz.le) (abs_nonneg _)
    _ = _ := by ring
  calc
    _ ≤ (((n.factorial : ℝ) * 4 ^ n) * Real.exp (|t| / 4)) * Real.exp (|t| / 4) :=
      mul_le_mul hpoly (Real.exp_le_exp.mpr hz') (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

private theorem primaryExpMoment_integrable (a : X → ℂ) (L : X → ℝ)
    (ha : AEStronglyMeasurable a μ) (hL : Measurable L)
    (hm : Integrable (fun x ↦ ‖a x‖ * Real.exp (|L x| / 2)) μ) (n : ℕ) :
    Integrable (fun x ↦ a x * (L x : ℂ) ^ n) μ := by
  apply (hm.const_mul ((n.factorial : ℝ) * 4 ^ n)).mono'
    (ha.mul (((Complex.continuous_ofReal.measurable.comp hL).pow_const _).aestronglyMeasurable))
  refine .of_forall fun x ↦ ?_
  change ‖a x * (L x : ℂ)^n‖ ≤ (n.factorial : ℝ) * 4 ^ n * (‖a x‖ * Real.exp (|L x|/2))
  have h := mul_le_mul_of_nonneg_left
    (primaryExpMoment_bound n 0 (by norm_num) (L x)) (norm_nonneg (a x))
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.zero_re,
    zero_mul, mul_zero, Real.exp_zero, mul_one, mul_assoc, mul_comm, mul_left_comm] using h

/-- Local logarithmic moments differentiate a weighted Laplace kernel. -/
private theorem primaryExpMoment_hasDeriv (a : X → ℂ) (L : X → ℝ)
    (ha : AEStronglyMeasurable a μ) (hL : Measurable L)
    (hmajor : Integrable (fun x ↦ ‖a x‖ * Real.exp (|L x| / 2)) μ)
    (n : ℕ) (z : ℂ) (hz : z ∈ Metric.ball 0 (1/4)) :
    HasDerivAt (fun w : ℂ ↦ ∫ x, a x * (L x : ℂ) ^ n * Complex.exp (w * L x) ∂μ)
      (∫ x, a x * (L x : ℂ) ^ (n+1) * Complex.exp (z * L x) ∂μ) z := by
  let H (k : ℕ) (w : ℂ) (x : X) := a x * (L x : ℂ) ^ k * Complex.exp (w * L x)
  let B (k : ℕ) (x : X) := ((k.factorial : ℝ) * 4 ^ k) * (‖a x‖ * Real.exp (|L x| / 2))
  have hm (k : ℕ) (w : ℂ) : AEStronglyMeasurable (H k w) μ := by
    have hLc := Complex.continuous_ofReal.measurable.comp hL
    exact (ha.mul (hLc.pow_const _).aestronglyMeasurable).mul
      ((Complex.continuous_exp.measurable.comp (hLc.const_mul w)).aestronglyMeasurable)
  have hb (k : ℕ) : Integrable (B k) μ := hmajor.const_mul _
  have hbound (k : ℕ) (w : ℂ) (hw : w ∈ Metric.ball 0 (1/4)) (x : X) : ‖H k w x‖ ≤ B k x := by
    simp only [H, B, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have h := mul_le_mul_of_nonneg_left (primaryExpMoment_bound k w (mem_ball_zero_iff.mp hw) (L x)) (norm_nonneg (a x))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := H n) (F' := H (n+1))
    (bound := B (n+1)) (Metric.isOpen_ball.mem_nhds hz) (.of_forall (hm n))
    ((hb n).mono' (hm n z) (.of_forall (hbound n z hz))) (hm (n+1) z)
    (.of_forall fun x w hw ↦ hbound _ w hw x) (hb _) ?_).2
  refine .of_forall fun x w _ ↦ ?_
  have h := ((hasDerivAt_id w).mul_const (L x : ℂ)).cexp.const_mul (a x * (L x : ℂ) ^ n)
  simpa only [H, id_eq, one_mul, mul_one, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

private theorem primaryExpMoment_iteratedDeriv (a : X → ℂ) (L : X → ℝ)
    (ha : AEStronglyMeasurable a μ) (hL : Measurable L)
    (hmajor : Integrable (fun x ↦ ‖a x‖ * Real.exp (|L x| / 2)) μ) (n : ℕ) :
    iteratedDeriv n (fun w : ℂ ↦ ∫ x, a x * Complex.exp (w * L x) ∂μ) 0 =
      ∫ x, a x * (L x : ℂ) ^ n ∂μ := by
  let M (k : ℕ) (w : ℂ) := ∫ x, a x * (L x : ℂ) ^ k * Complex.exp (w * L x) ∂μ
  have h (k : ℕ) : EqOn (iteratedDeriv k (M 0)) (M k) (Metric.ball 0 (1/4)) := by
    induction k with
    | zero => exact fun _ _ ↦ rfl
    | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      exact ((ih.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz)).deriv_eq).trans
        (primaryExpMoment_hasDeriv a L ha hL hmajor k z hz).deriv
  simpa only [M, pow_zero, mul_one, zero_mul, Complex.exp_zero] using h n
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1/4))

end

private theorem primaryMellin_integralAverage {H G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (μ : Measure G) [μ.IsMulRightInvariant] [SFinite μ] (ν : Measure H) [IsFiniteMeasure ν]
    (i : H → G) (hi : Continuous i) (f : G → ℂ) (hf : Continuous f)
    (c : G →ₜ* ℂ) (ω : H → ℂ) (hω : ∀ h, c (i h) = ω h)
    (hfc : Integrable (fun g ↦ f g * c g) μ) :
    (∫ g, (∫ u, f (g * i u) * ω u ∂ν) * c g ∂μ) =
      (ν.real univ : ℂ) * ∫ g, f g * c g ∂μ := by
  let A (g : G) := f g * c g
  have hA : Continuous A := hf.mul c.continuous
  have hprod : Integrable (uncurry (fun u g ↦ A (g * i u))) (ν.prod μ) := by
    have hc : Continuous (fun p : H × G ↦ A (p.2 * i p.1)) :=
      hA.comp (continuous_snd.mul (hi.comp continuous_fst))
    apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
    refine ⟨.of_forall fun u ↦ ?_, ?_⟩
    · exact (measurePreserving_mul_right μ (i u)).integrable_comp_of_integrable hfc
    · exact (integrable_const (∫ g, ‖A g‖ ∂μ)).congr (.of_forall fun u ↦
        (integral_mul_right_eq_self (fun g ↦ ‖A g‖) (i u)).symm)
  calc
    _ = ∫ g, (∫ u, A (g * i u) ∂ν) ∂μ := by
      refine integral_congr_ae (.of_forall fun g ↦ ?_)
      change (∫ u, f (g * i u) * ω u ∂ν) * c g = _
      rw [← integral_mul_const]
      apply integral_congr_ae
      exact .of_forall fun u ↦ by simp only [A, map_mul, hω]; ring
    _ = ∫ u, (∫ g, A (g * i u) ∂μ) ∂ν := (integral_integral_swap hprod).symm
    _ = _ := by simp only [integral_mul_right_eq_self, integral_const, Complex.real_smul]; rfl

local notation "Gₛ" => SIdeleQuotient F S
local notation "Kₛ" => (sIdeleQuotientNorm F S).ker
local notation "Aₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Qₛ" => QuasiCharacter Gₛ

private local instance primaryNormKernelMeasurable : MeasurableSpace Kₛ := borel _
local notation "μₛ" => sLocalQuotientTamagawaMeasure F S
local notation "μ₁" => sLocalNormOneQuotientMeasure F S

/-- The projected Mellin transform equals the continued zeta function times the
total mass of the norm-one fiber on its half-plane of absolute convergence. -/
private theorem primaryMellin_homogeneous [SecondCountableTopology Gₛ] [SecondCountableTopology Kₛ] [LocallyCompactSpace Gₛ] [T2Space Gₛ] (ω : PontryaginDual Kₛ)
    (c : Qₛ) (hc : ∃ (χ : PontryaginDual Gₛ) (s : ℂ), 0 < s.re ∧ c = quasiCharacterNormTwist
      (G := Gₛ) (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) s)
    (hr : ∀ u : Kₛ, c u.val = (ω u : ℂ)) (f : Aₛ) :
    (∫ g, sLocalHomogeneousAdelicThetaLinearMap F S ω f g * c g ∂μₛ) =
      ((μ₁).real univ : ℂ) * sLocalIdelicZFunction f c := by
  let : BorelSpace Gₛ := ⟨rfl⟩
  let : BorelSpace Kₛ := ⟨rfl⟩
  let : CompactSpace Kₛ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : (μ₁).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : (μₛ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  let : (μₛ).IsMulRightInvariant := ⟨fun g ↦ by simpa only [mul_comm g] using (map_mul_left_eq_self μₛ g)⟩
  have h := primaryMellin_integralAverage μₛ μ₁ (fun u : Kₛ ↦ u.val) continuous_subtype_val
    (sLocalAdelicThetaOnClasses F S f) (sLocalAdelicThetaOnClasses F S f).continuous c
    (fun u ↦ (ω u : ℂ)) hr (sLocalThetaMellinIntegral_integrable f c hc)
  change _ = ((μ₁).real univ : ℂ) * sLocalThetaMellinIntegral f c at h
  exact h.trans (congrArg (((μ₁).real univ : ℂ) * ·) (((sLocalThetaMellinIntegral_eq_zeta f hc).trans
    (sLocalIdelicZFunction_eq_integral f hc).symm)))

local notation "νmass" => ((μ₁).real univ : ℂ)
local notation "cnorm(" g ")" => ((((sIdeleQuotientNorm F S (g)).val : ℝ)) : ℂ)
local notation "llog(" g ")" => Real.log (((sIdeleQuotientNorm F S (g)).val : ℝ))
local notation "chartₛ(" ξ ", " w ")" => quasiCharacterNormTwist (G := Gₛ) (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (ξ)) (w)

private theorem primaryMellin_chart_value (ξ : PontryaginDual Gₛ) (z : ℂ) (g : Gₛ) :
    chartₛ(ξ, 1-z) g = (ξ g : ℂ) * cnorm(g) * Complex.exp (z * (-(llog(g)) : ℝ)) := by
  have hp : 0 < ((sIdeleQuotientNorm F S g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change (ξ g : ℂ) * cnorm(g) ^ (1-z) = _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, mul_sub, mul_one, sub_eq_add_neg, Complex.exp_add,
    ← Complex.ofReal_exp, Real.exp_log hp, Complex.ofReal_neg, mul_neg, mul_comm z]
  ring

private theorem primaryMellin_reflectedJet [SecondCountableTopology Gₛ] [SecondCountableTopology Kₛ] [LocallyCompactSpace Gₛ] [T2Space Gₛ]
    (ω : PontryaginDual Kₛ) (ξ : PontryaginDual Gₛ) (hξ : ∀ u : Kₛ, ξ u.val = ω u)
    (f : Aₛ) (Y : Gₛ → ℂ) (hY : Continuous Y)
    (hval : ∀ g, Y g = cnorm(g) * sLocalHomogeneousAdelicThetaLinearMap F S ω f g)
    (hmajor : Integrable (fun g ↦ ‖Y g * (ξ g : ℂ)‖ * Real.exp (|-(llog(g))|/2)) μₛ)
    (k : ℕ) :
    iteratedDeriv k (fun z : ℂ ↦ sLocalIdelicZFunction f (chartₛ(ξ, 1-z))) 0 =
      νmass⁻¹ * (-1 : ℂ) ^ k * ∫ g, Y g * (ξ g : ℂ) * (llog(g) : ℂ) ^ k ∂μₛ := by
  let : BorelSpace Gₛ := ⟨rfl⟩
  let : BorelSpace Kₛ := ⟨rfl⟩
  let : CompactSpace Kₛ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : (μ₁).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hm : νmass ≠ 0 := Complex.ofReal_ne_zero.mpr (MeasureTheory.measureReal_univ_pos (μ := μ₁)).ne'
  let L (g : Gₛ) := -(llog(g))
  let a (g : Gₛ) := νmass⁻¹ * (Y g * (ξ g : ℂ))
  have hL : Continuous L := ((NNReal.continuous_coe.comp (Units.continuous_val.comp
    (isProperMap_sIdeleQuotientNorm F S).continuous)).log fun g ↦
      NNReal.coe_ne_zero.mpr (sIdeleQuotientNorm F S g).ne_zero).neg
  have ha : Continuous a := continuous_const.mul (hY.mul (continuous_subtype_val.comp ξ.continuous))
  have hmaj : Integrable (fun g ↦ ‖a g‖ * Real.exp (|L g| / 2)) μₛ := by
    simpa only [a, L, norm_mul, mul_assoc] using hmajor.const_mul ‖νmass⁻¹‖
  have hEq : (fun z : ℂ ↦ sLocalIdelicZFunction f (chartₛ(ξ, 1-z))) =ᶠ[𝓝 0]
      (fun z ↦ ∫ g, a g * Complex.exp (z * L g) ∂μₛ) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1/4)] with z hz
    let d : Qₛ := chartₛ(ξ, 1-z)
    have hd (u : Kₛ) : d u.val = (ω u : ℂ) := by
      change (ξ u.val : ℂ) * cnorm(u.val) ^ (1-z) = _
      rw [show sIdeleQuotientNorm F S u.val = 1 from u.property, Units.val_one, NNReal.coe_one,
        Complex.ofReal_one, Complex.one_cpow, mul_one, hξ]
    have hpos : 0 < (1-z).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith [Complex.re_le_norm z, mem_ball_zero_iff.mp hz]
    have h := primaryMellin_homogeneous (F := F) (S := S) ω d ⟨ξ, 1-z, hpos, rfl⟩ hd f
    change sLocalIdelicZFunction f d = _
    calc
      _ = νmass⁻¹ * (νmass * sLocalIdelicZFunction f d) := (inv_mul_cancel_left₀ hm _).symm
      _ = _ := by
        rw [← h, ← integral_const_mul]
        refine integral_congr_ae (.of_forall fun g ↦ ?_)
        change νmass⁻¹ * (sLocalHomogeneousAdelicThetaLinearMap F S ω f g * d g) =
          (νmass⁻¹ * (Y g * (ξ g : ℂ))) * Complex.exp (z * L g)
        rw [hval, show d g = _ from primaryMellin_chart_value (F := F) (S := S) ξ z g]
        ring
  rw [hEq.iteratedDeriv_eq k, primaryExpMoment_iteratedDeriv a L ha.aestronglyMeasurable hL.measurable hmaj,
    ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun g ↦ ?_)
  change νmass⁻¹ * (Y g * (ξ g : ℂ)) * ((-(llog(g)) : ℝ) : ℂ)^k = _
  rw [Complex.ofReal_neg, neg_pow]
  ring


private theorem primaryDecay_momentMajorant {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) [μ.IsHaarMeasure]
    (I : Set ℝ) (hI : (1/2 : ℝ) ∈ I ∧ (-1/2 : ℝ) ∈ I)
    (y : ModulatedExponentialDecay m I) (hc : Continuous y.val) (ξ : PontryaginDual G) :
    Integrable (fun g ↦ ‖y.val g * (ξ g : ℂ)‖ * Real.exp (|-(Real.log ((m g).val : ℝ))| / 2)) μ := by
  let L (g : G) := Real.log ((m g).val : ℝ)
  have hL : Continuous L := (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
    fun g ↦ NNReal.coe_ne_zero.mpr (m g).ne_zero
  have hwt (a : I) : Integrable (fun x ↦ ‖y.val x‖ * Real.exp (a * L x)) μ := by
    let f := modulatedExponentialDecayTwist m I a y
    have hf := ((schwartzBruhat_fourier_equiv (G := G) μ).choose_spec f).1.norm
    refine hf.congr (.of_forall fun x ↦ ?_)
    change ‖(((((m x).val : ℝ) ^ (a : ℝ) : ℝ) : ℂ) * y.val x)‖ = _
    have hp : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp _),
      Real.rpow_def_of_pos hp, mul_comm (Real.log _), mul_comm (Real.exp _)]
  have hm := (hwt ⟨_, hI.1⟩).add (hwt ⟨_, hI.2⟩)
  simp only [norm_mul, Circle.norm_coe, mul_one, abs_neg]
  apply hm.mono' (hc.norm.mul (hL.abs.div_const 2).rexp).aestronglyMeasurable
  refine .of_forall fun x ↦ ?_
  change ‖‖y.val x‖ * Real.exp (|L x| / 2)‖ ≤
    ‖y.val x‖ * Real.exp (1/2 * L x) + ‖y.val x‖ * Real.exp ((-1/2) * L x)
  rw [Real.norm_of_nonneg (by positivity)]
  rcases le_total 0 (L x) with hx | hx
  · rw [abs_of_nonneg hx, show L x / 2 = 1/2 * L x by ring]
    exact le_add_of_nonneg_right (by positivity)
  · rw [abs_of_nonpos hx, show -(L x) / 2 = (-1/2) * L x by ring]
    exact le_add_of_nonneg_left (by positivity)
local notation "N(" x ")" => (((sIdeleQuotientNorm F S x).val : ℝ) : ℂ)
local notation "θ(" ω ", " f ")" => sLocalHomogeneousAdelicThetaLinearMap F S ω f

private theorem primaryFourier_surjective : Surjective (sAdeleSchwartzFourier (F := F) (S := S)) := by
  intro u
  refine ⟨sAdeleSchwartzFourier (sAdeleSchwartzFourier (sAdeleSchwartzFourier u)), ?_⟩
  apply Subtype.ext
  funext x
  exact (sLocal_fourier_inversion (sAdeleSchwartzFourier (sAdeleSchwartzFourier u)) x.toAdd).trans
    ((sLocal_fourier_inversion u (-x.toAdd)).trans
      (congrArg (fun y ↦ u (Multiplicative.ofAdd y)) (neg_neg x.toAdd)))

private theorem allExponents_normDiv {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    (n : H →ₜ* ℝ≥0ˣ) (y : ↥(modulatedExponentialDecaySubmodule n univ)) :
    ∃ z : ↥(modulatedExponentialDecaySubmodule n univ), ∀ g : H, z.val g = y.val g / (((n g).val : ℝ) : ℂ) := by
  let Z (g : H) := y.val g / (((n g).val : ℝ) : ℂ)
  have hz : Z ∈ modulatedExponentialDecaySubmodule n univ := by
    refine (Submodule.mem_iInf _).mpr fun a ↦ Submodule.mem_comap.mpr ?_
    have h (g : H) : (modulationWeight n a.val Z) g = (modulationWeight n (a.val-1) y.val) g := by
      have hp : 0 < ((n g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
      change (((((n g).val : ℝ) ^ a.val : ℝ) : ℂ) * (y.val g / (((n g).val : ℝ) : ℂ))) =
        (((((n g).val : ℝ) ^ (a.val-1) : ℝ) : ℂ) * y.val g)
      rw [Real.rpow_sub hp, Real.rpow_one, Complex.ofReal_div]
      ring
    rw [funext h]
    exact modulationWeight_mem_schwartzBruhat n univ ⟨a.val-1, trivial⟩ y
  exact ⟨⟨Z, hz⟩, fun _ ↦ rfl⟩

private theorem primaryAllExponents_quotientNorm_covariant (u : J₁) (g : Jₛ) :
    N(u.val⁻¹ * g) = N(g) := by
  rw [map_mul, map_inv, show sIdeleQuotientNorm F S u.val = 1 from u.property, inv_one, one_mul]

private theorem primaryAllExponents_fourier_lift (ω : PontryaginDual J₁)
    (y : sLocalDecayIsotype (F := F) (S := S) univ ω) :
    ∃ f : ℬₛ, ∀ g : Jₛ, N(g) * θ(ω, sAdeleSchwartzFourier f) g = y.val.val g := by
  have hprop := (mem_sLocalDecayIsotype (F := F) (S := S) univ ω y.val).mp y.property
  let n : Jₛ →ₜ* ℝ≥0ˣ := mGroup
  have hDiv := allExponents_normDiv (H := Jₛ) n
  obtain ⟨z, hz⟩ := hDiv ⟨y.val.val, y.val.property⟩
  have hmem : z ∈ sLocalDecayIsotype (F := F) (S := S) univ ω := by
    refine (mem_sLocalDecayIsotype (F := F) (S := S) univ ω z).mpr fun u g ↦ ?_
    have hq := primaryAllExponents_quotientNorm_covariant (F := F) (S := S) u g
    calc
      z.val (u.val⁻¹ * g) = y.val.val (u.val⁻¹ * g) / N(u.val⁻¹ * g) := hz _
      _ = ((ω u : ℂ) * y.val.val g) / N(g) := congrArg₂ (· / ·) (hprop u g) hq
      _ = (ω u : ℂ) * z.val g := (mul_div_assoc _ _ _).trans (congrArg ((ω u : ℂ) * ·) (hz g).symm)
  obtain ⟨e, he⟩ := sLocalThetaPoleBound_zero_equiv_decay (F := F) (S := S) ω
  obtain ⟨a, ha⟩ := e.surjective ⟨z, hmem⟩
  obtain ⟨f₁, hf₁⟩ := (sLocalHomogeneousAdelicThetaLinearMap F S ω).ker.mkQ_surjective a.val
  obtain ⟨f, hf⟩ := primaryFourier_surjective (F := F) (S := S) f₁
  refine ⟨f, fun g ↦ ?_⟩
  have hs := he a f₁ hf₁.symm g
  change N(g) * (sLocalHomogeneousAdelicThetaLinearMap F S ω (sAdeleSchwartzFourier f)) g = _
  rw [hf, ← hs, ha]
  change N(g) * z.val g = _
  rw [hz]
  change N(g) * (y.val.val g / N(g)) = _
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (sIdeleQuotientNorm F S g).ne_zero))


private theorem primaryDecay_continuous
    {I : Set ℝ} (h0 : 0 ∈ I) (y : ModulatedExponentialDecay mGroup I) :
    Continuous y.val := by
  let f := modulatedExponentialDecayTwist mGroup I ⟨0, h0⟩ y
  exact (schwartzBruhat_continuous f).congr fun g ↦
    (modulatedExponentialDecayTwist_apply mGroup I ⟨0, h0⟩ y g).trans (by simp)

private theorem primaryDecay_logMoment_integrable
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (hI : (1/2 : ℝ) ∈ I ∧ (-1/2 : ℝ) ∈ I)
    (y : ModulatedExponentialDecay mGroup I) (ξ : PontryaginDual Jₛ) (r : ℕ) :
    Integrable (fun g ↦ y.val g * (ξ g : ℂ) * (Real.log ((mₛ g).val : ℝ) : ℂ) ^ r) μorb := by
  have hc := primaryDecay_continuous h0 y
  let L (g : Jₛ) := Real.log (((mGroup) g).val : ℝ)
  have hL : Continuous L :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (mGroup).continuous)).log
      fun g ↦ NNReal.coe_ne_zero.mpr (mₛ g).ne_zero
  apply primaryExpMoment_integrable (fun g ↦ y.val g * (ξ g : ℂ)) L
    (hc.mul (continuous_subtype_val.comp ξ.continuous)).aestronglyMeasurable hL.measurable
  simpa only [L, abs_neg] using primaryDecay_momentMajorant mGroup μorb I hI y hc ξ

local notation "logNorm" g => Real.log ((mₛ g).val : ℝ)

private def sLocalOrbital_logMoment (ξ : PontryaginDual Jₛ) (k : ℕ) (f : Jₛ → ℂ) : ℂ :=
  ∫ g, f g * (ξ g : ℂ) * (logNorm g : ℂ) ^ k ∂μorb

open scoped Classical in
/-- The polynomial annihilation result applies to a difference product on any
decay interval for which the log moments are integrable. -/
private theorem sLocalOrbital_differenceMoment_ambient {G : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hs : Surjective m)
    (ω : PontryaginDual m.toMonoidHom.ker) (μ : Measure G) [μ.IsHaarMeasure]
    (I : Set ℝ) (hInt : OrdConnected I) (h0 : 0 ∈ I) (L : List G)
    (ξ : PontryaginDual G) (k : ℕ)
    (hdeg : (Polynomial.X ^ k : Polynomial ℂ).degree <
      (L.countP (fun g ↦ decide (ξ ∈ modulatedCyclicAnnihilatorFiber m ω g)) : WithBot ℕ))
    (hint : ∀ (y : ModulatedExponentialDecay m I) (r : ℕ),
      Integrable (fun x ↦ y.val x * (ξ x : ℂ) * (Real.log ((m x).val : ℝ) : ℂ)^r) μ)
    (f : ModulatedExponentialDecay m I) :
    ∫ g, (modulatedDifferenceProduct m hm hs I hInt ⟨0, h0⟩ L f).val g *
      (ξ g : ℂ) * (Real.log ((m g).val : ℝ) : ℂ)^k ∂μ = 0 := by
  classical
  let D := modulatedDifferenceProduct m hm hs I hInt ⟨0, h0⟩
  let v (l : List G) (g : G) := (D l f).val g
  have hdiff (g : G) (l : List G) (x : G) : v (g :: l) x = v l x - v l (g * x) := by
    let Δ := modulatedCyclicDifference m g hm hs I hInt ⟨0, h0⟩
    have hstep : D (g :: l) f = Δ (D l f) := by
      simp only [D, Δ, modulatedDifferenceProduct, List.map_cons, List.prod_cons, mul_apply_eq_comp]
    exact (congrArg (fun q : ModulatedExponentialDecay m I ↦ q.val x) hstep).trans
      (modulatedCyclicDifference_apply m g hm hs I hInt ⟨0, h0⟩ (D l f) x)
  have h := integral_differenceProduct_polynomial m ω μ ξ v hdiff
    (fun l r ↦ hint (D l f) r) L (Polynomial.X ^ k) hdeg
  change (∫ g, v L g * (ξ g : ℂ) * (Real.log ((m g).val : ℝ) : ℂ)^k ∂μ) = 0
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, mul_assoc] using h

/-- Log moments vanish below the multiplicity of the periodic quotient, also
on the half-line used for the norm-weighted Fourier component. -/
private theorem sLocalOrbital_logMoment_difference_zero (p : Vℚ) (ω : PontryaginDual J₁)
    (j : ModelIndex(p, ω)) :
    let L := List.ofFn (sLocalOrbitalDifferenceGenerator p ω)
    let R := (modulatedIsotypicDifferenceProduct mGroup sLocalOrbital_modulation.1
      sLocalOrbital_modulation.2 ω⁻¹ I₋ ordConnected_Ioi hI₋ L).range
    ∀ y : H₋(ω⁻¹), y ∈ R → sLocalOrbital_logMoment j.val.1 j.val.2 y.val.val = 0 := by
  classical
  intro L R y hy
  let f := hy.choose
  have hf : _ = y := hy.choose_spec
  have hk : j.val.2 < L.countP
      (fun g ↦ decide (j.val.1 ∈ modulatedCyclicAnnihilatorFiber mGroup ω⁻¹ g)) := by
    simpa only [L, List.countP_ofFn, modulatedPeriodicMultiplicity, decide_eq_true_eq] using j.property
  have hdeg : (Polynomial.X ^ j.val.2 : Polynomial ℂ).degree <
      (L.countP (fun g ↦ decide (j.val.1 ∈ modulatedCyclicAnnihilatorFiber mGroup ω⁻¹ g)) : WithBot ℕ) := by
    rw [Polynomial.degree_X_pow]
    exact WithBot.coe_lt_coe.mpr hk
  have hi := sLocalOrbital_differenceMoment_ambient mGroup sLocalOrbital_modulation.1
    sLocalOrbital_modulation.2 ω⁻¹ μorb I₋ ordConnected_Ioi hI₋ L j.val.1 j.val.2 hdeg
    (fun q r ↦ primaryDecay_logMoment_integrable I₋ hI₋ (by constructor <;> norm_num) q j.val.1 r) f.val
  have hD := modulatedIsotypicDifferenceProduct_apply_coe mGroup sLocalOrbital_modulation.1
    sLocalOrbital_modulation.2 ω⁻¹ I₋ ordConnected_Ioi hI₋ L f
  have he := congrArg (fun z : ModulatedExponentialDecay mGroup I₋ ↦
    sLocalOrbital_logMoment j.val.1 j.val.2 z.val) (congrArg Subtype.val hf.symm |>.trans hD)
  exact he.trans hi

/-- The norm twist removes the real shift in the dual character, while reflection
contributes one minus sign per logarithmic derivative. -/
private theorem sLocalOrbital_shiftedFourierJet (p : Vℚ) (ω : PontryaginDual J₁)
    (j : ModelIndex(p, ω)) (i : Idx(p, ω))
    (hi : i.val = (((circleToComplex).comp j.val.1⁻¹), j.val.2))
    (f : ℬₛ) (y : H₋(ω⁻¹))
    (hy : ∀ g : Jₛ, y.val.val g = (((mₛ g).val : ℝ) : ℂ) *
      sLocalHomogeneousAdelicThetaLinearMap F S ω⁻¹ (sAdeleSchwartzFourier f) g) :
    sLocalOrbitalFourierJet i ((Kₛ(ω)).mkQ f) =
      (((sLocalNormOneQuotientMeasure F S).real univ : ℂ)⁻¹ * (-1 : ℂ)^j.val.2) *
        sLocalOrbital_logMoment j.val.1 j.val.2 y.val.val := by
  let : SecondCountableTopology Kₛ := IsEmbedding.subtypeVal.secondCountableTopology
  have hc := primaryDecay_continuous hI₋ y.val
  have hmajor := primaryDecay_momentMajorant mGroup μorb I₋ (by constructor <;> norm_num) y.val hc j.val.1
  have hrestr := sLocalOrbitalModelIndex_restrict p ω j
  have h := primaryMellin_reflectedJet ω⁻¹ j.val.1 hrestr (sAdeleSchwartzFourier f)
    y.val.val hc hy hmajor j.val.2
  have heq : fourierZeta(i.val.1) f =
      fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(j.val.1) (1 - z)) := by
    have hchar : i.val.1 = (circleToComplex).comp j.val.1⁻¹ := congrArg Prod.fst hi
    funext z
    change sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (twistₛ i.val.1 z)) = _
    apply congrArg (sLocalIdelicZFunction (sAdeleSchwartzFourier f))
    rw [hchar]
    exact (sLocal_dual_normTwist j.val.1⁻¹ z).trans
      (congrArg (fun ξ : PontryaginDual Jₛ ↦ chart(ξ) (1 - z)) (inv_inv j.val.1))
  calc
    _ = iteratedDeriv i.val.2 (fourierZeta(i.val.1) f) 0 := sLocalOrbitalFourierJet_mk i f
    _ = _ := by
      rw [heq, show i.val.2 = j.val.2 from congrArg Prod.snd hi]
      exact h

open Classical in
/-- Paper: Theorem 7.3.1.6(1), p. 345.
Each primary polar functional vanishes on the primary principal-value image, so it descends
to a continuous functional on the p-primary orbital quotient. -/
private theorem sLocalPolarOrbital_bases_of_laurent_bounds_descend
    (p : Vℚ) (ω : PontryaginDual J₁) :
    ∃ D : Idx(p, ω) → StrongDual ℂ (Q(p, ω)),
      ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x := by
  refine ⟨fun j ↦ (Rₚ(p, ω)).liftQL
      (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j)
      (sLocalOrbitalPrincipalPart_range_le_ker (F := F) (S := S) p ω j), fun j x ↦ ?_⟩
  rfl

open Classical in
/-- Paper: Theorem 7.3.1.2(2), p. 341.
The selected primary coefficients have a biorthogonal family in the p-primary orbital
quotient. This is the biorthogonality used in Theorem 7.3.1.6(3), obtained from the
biorthogonal family of the primary principal-value operator. -/
private theorem sLocalPolarOrbital_bases_of_laurent_bounds_biorthogonal
    (p : Vℚ) (ω : PontryaginDual J₁)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) :
    ∃ ψ : Idx(p, ω) → Q(p, ω),
      ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x =
          if i = j then 1 else 0 :=
  sLocalOrbitalPrincipalValue_biorthogonal (F := F) (S := S) (T := Sₚ(p)) (hₚ(p))
    _hp _hS _hPic ω

/-- Absolute summability in every continuous seminorm gives convergence of the
coordinate series; biorthogonality and separation identify its sum. -/
private theorem sLocalPolarOrbital_bases_of_laurent_bounds_primal_of_summable
    (p : Vℚ) (ω : PontryaginDual J₁)
    (e : ℕ → Q(p, ω)) (d : ℕ → StrongDual ℂ (Q(p, ω)))
    (hF : IsFrechetTVS (Q(p, ω)))
    (hbi : ∀ m n, d m (e n) = if m = n then 1 else 0)
    (hsep : ∀ x, (∀ n, d n x = 0) → x = 0)
    (hsum : ∀ (q : Seminorm ℂ (Q(p, ω))), Continuous q →
      ∀ x, Summable (fun n ↦ q (d n x • e n))) :
    IsSchauderBasis e d ∧ SchauderBasis.IsAbsolute e d := by
  classical
  have hFcopy := hF
  obtain ⟨_, hpoly, hmet, hcomplete⟩ := hFcopy
  let : UniformSpace (Q(p, ω)) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (Q(p, ω)) := isUniformAddGroup_of_addCommGroup
  let P := fun q : {q : Seminorm ℂ (Q(p, ω)) // Continuous q} ↦ q.val
  have hP : WithSeminorms P := PolynormableSpace.withSeminorms ℂ (Q(p, ω))
  have hs (x : Q(p, ω)) : Summable (fun n ↦ d n x • e n) := by
    apply summable_iff_cauchySeq_finset.mpr
    rw [CauchySeq, cauchy_map_iff', uniformity_eq_comap_nhds_zero,
      Filter.tendsto_comap_iff, hP.tendsto_nhds]
    intro q ε hε
    let L : Q(p, ω) →ₗ[ℂ] LocalBanach (P q) :=
      UniformSpace.Completion.toComplL.toLinearMap.comp LinearMap.id
    have hL (y : Q(p, ω)) : ‖L y‖ = P q y := localBanach_norm_coe (P q) y
    have hnorm : Summable (fun n ↦ ‖L (d n x • e n)‖) := by
      simpa only [hL] using hsum q.val q.property x
    have hc := cauchy_map_iff'.mp
      (summable_iff_cauchySeq_finset.mp (Summable.of_norm hnorm))
    rw [tendsto_uniformity_iff_dist_tendsto_zero, Metric.tendsto_nhds] at hc
    filter_upwards [hc ε hε] with z hz
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_eq_norm',
      ← map_sum, ← map_sum, ← map_sub, hL] at hz
    simpa only [sub_zero, Function.comp_apply] using hz
  have hvalue (x : Q(p, ω)) : ∑' n, d n x • e n = x := by
    apply sub_eq_zero.mp
    apply hsep
    intro m
    have hm := (hs x).hasSum.mapL (d m)
    simp only [map_smul, hbi, smul_eq_mul, mul_ite, mul_one, mul_zero] at hm
    have he : d m (∑' n, d n x • e n) = d m x := by
      simpa using hm.tsum_eq.symm
    rw [map_sub, he, sub_self]
  have hb : IsSchauderBasis e d := ⟨hbi, fun x ↦ by
    have h := (hs x).hasSum
    rw [hvalue x] at h
    exact Tendsto.mono_left h (SummationFilter.conditional ℕ).le_atTop⟩
  exact ⟨hb, (SchauderBasis.isAbsolute_iff_summable_of_frechet hF hb).mpr hsum⟩


/-- Transport an absolute basis through a linear homeomorphism and rescale each
coordinate by a nonzero scalar, with the inverse rescaling on its dual vector. -/
private theorem orbitalQuotient_rescale_basis {Q U : Type*}
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    [AddCommGroup U] [Module ℂ U] [TopologicalSpace U]
    (T : Q ≃L[ℂ] U) (e : ℕ → U) (d : ℕ → StrongDual ℂ U)
    (hb : IsSchauderBasis e d) (ha : SchauderBasis.IsAbsolute e d)
    (s : ℕ → ℂ) (hs : ∀ n, s n ≠ 0) :
    let E := fun n ↦ (s n)⁻¹ • T.symm (e n)
    let D := fun n ↦ s n • (d n).comp T.toContinuousLinearMap
    IsSchauderBasis E D ∧ SchauderBasis.IsAbsolute E D := by
  intro E D
  have hterm (v : Q) (n : ℕ) : D n v • E n = T.symm (d n (T v) • e n) := by
    change (s n * d n (T v)) • ((s n)⁻¹ • T.symm (e n)) = _
    rw [map_smul, smul_smul, mul_assoc, mul_comm (d n (T v)), ← mul_assoc,
      mul_inv_cancel₀ (hs n), one_mul]
  constructor
  · refine ⟨fun m n ↦ ?_, fun v ↦ ?_⟩
    · have hmn : d m (e n) = if m = n then 1 else 0 := hb.1 m n
      change s m * d m (T ((s n)⁻¹ • T.symm (e n))) = _
      rw [map_smul, T.apply_symm_apply, map_smul, hmn]
      by_cases h : m = n
      · subst n
        simp [smul_eq_mul, hs m]
      · simp [h]
    · have h := (hb.2 (T v)).mapL T.symm.toContinuousLinearMap
      change HasSum (fun n ↦ T.symm (d n (T v) • e n)) (T.symm (T v))
        (SummationFilter.conditional ℕ) at h
      rw [T.symm_apply_apply] at h
      simp_rw [← hterm] at h
      exact h
  · intro q hq
    obtain ⟨p, hp, h⟩ := ha (q.comp T.symm.toLinearMap) (hq.comp T.symm.continuous)
    refine ⟨p.comp T.toLinearMap, hp.comp T.continuous, fun v ↦ ?_⟩
    have hv := h (T v)
    change Summable (fun n ↦ q (T.symm (d n (T v) • e n))) ∧
      (∑' n, q (T.symm (d n (T v) • e n))) ≤ p (T v) at hv
    change _ ∧ _ ≤ p (T v)
    simpa only [hterm] using hv


/-- A nuclear Fréchet primary quotient is reflexive, so its absolute basis has
an unconditional dual basis, with the usual evaluation coefficients. -/
private theorem sLocalOrbital_dual_of_absolute (p : Vℚ) (ω : PontryaginDual J₁)
    (hS : IsSaturatedPlaceSet S) (hp : (Sₚ(p)).Nonempty) (hPic : PicTrivial)
    (e : ℕ → Q(p, ω)) (d : ℕ → StrongDual ℂ (Q(p, ω)))
    (hb : IsSchauderBasis e d) (ha : SchauderBasis.IsAbsolute e d) :
    let ev := fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (e n)
    IsSchauderBasis d ev ∧ SchauderBasis.IsUnconditional d ev ∧
      IsSchauderBasis e d ∧ SchauderBasis.IsAbsolute e d := by
  let Q := Q(p, ω)
  have hclosed : IsClosed (Rₚ(p, ω) : Set (Θₛ(ω))) := by
    have heq : (Rₚ(p, ω) : Set (Θₛ(ω))) = ⋂ j : Idx(p, ω), (sLocalOrbitalFourierJet j).ker := by
      ext x
      rw [Set.mem_iInter]
      change x ∈ Rₚ(p, ω) ↔ ∀ j : Idx(p, ω), sLocalOrbitalFourierJet j x = 0
      exact sLocalOrbitalFourierJet_commonKer p ω hS hp hPic x
    exact heq ▸ isClosed_iInter fun j ↦ (sLocalOrbitalFourierJet j).isClosed_ker
  have hF : IsFrechetTVS Q := isFrechetTVS_quotient
    (sLocalHomogeneousThetaSpace_frechet ω) (Rₚ(p, ω)) hclosed
  have hN : IsNuclearTVS.{0} Q := isNuclearTVS_quotient
    (sLocalHomogeneousThetaSpace_nuclear ω) (Rₚ(p, ω))
  let : BarrelledSpace ℂ Q := isFrechetTVS_barrelled hF
  let : PolynormableSpace ℂ Q := hF.choose_spec.1
  let : TopologicalSpace.MetrizableSpace Q := hF.choose_spec.2.1
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  let : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  let hComplete : CompleteSpace Q := hF.choose_spec.2.2
  let : CompleteSpace Q := hComplete
  let : MontelSpace ℂ Q := ⟨fun K hK hbounded ↦ by
    simpa only [hK.closure_eq] using isCompact_closure_of_isNuclearTVS Q hN hbounded⟩
  have hreflexive : IsHomeomorph (ContinuousLinearMap.applyₗ (E := Q) ℂ (RingHom.id ℂ)) :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨isEmbedding_strongBidual_eval, surjective_strongBidual_eval⟩
  exact ⟨SchauderBasis.isShrinking_of_isAbsolute hComplete hreflexive hb ha,
    SchauderBasis.strongDual_isUnconditional_of_isAbsolute hComplete hreflexive hb ha, hb, ha⟩

/-- A coefficient comparison with a Schauder basis determines the kernel of
the comparison map. -/
private theorem orbitalQuotient_kernel_of_coefficients {E U I J : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup U] [Module ℂ U] [TopologicalSpace U] [T2Space U]
    (C : E →L[ℂ] U) (R : Submodule ℂ E)
    (F : I → E → ℂ) (d : J → StrongDual ℂ U) (ι : J ≃ I) (s : J → ℂ)
    (hs : ∀ j, s j ≠ 0) (hF : ∀ x, x ∈ R ↔ ∀ i, F i x = 0)
    (hD : ∀ j x, F (ι j) x = s j * d j (C x))
    (σ : ℕ ≃ J) (e : ℕ → U) (hb : IsSchauderBasis e (d ∘ σ)) :
    C.ker = R := by
  ext x
  change C x = 0 ↔ x ∈ R
  rw [hF x]
  constructor
  · intro h i
    have h0 := hD (ι.symm i) x
    rw [ι.apply_symm_apply, h, map_zero, mul_zero] at h0
    exact h0
  · intro h
    have hall (n : ℕ) : d (σ n) (C x) = 0 :=
      (mul_eq_zero.mp ((hD (σ n) x).symm.trans (h (ι (σ n))))).resolve_left (hs _)
    have hsum := hb.2 (C x)
    change HasSum (fun n ↦ d (σ n) (C x) • e n) (C x) (SummationFilter.conditional ℕ) at hsum
    simp only [hall, zero_smul] at hsum
    exact hsum.unique hasSum_zero

-- TODO(paper-gap): In (7.3.1.19) use the inverse uniformizers at the unramified
-- places above p for the generators of Chapter 4. At a ramified place Weil's
-- unit average vanishes on the isotype, and its principal value is the identity.
/-- The primary generators have positive log-periods commensurate with the log of
the residue cardinality of the rational prime. -/
private theorem sLocalOrbitalDifferenceGenerator_periods (p : Vℚ) (ω : PontryaginDual J₁) :
    (∀ k, 1 < (mGroup (sLocalOrbitalDifferenceGenerator p ω k)).val) ∧
    ∃ a : ℝ, 0 < a ∧ ∀ i, ∃ r : ℚ,
      Real.log ((mGroup (sLocalOrbitalDifferenceGenerator p ω i)).val : ℝ) = (r : ℝ) * a := by
  classical
  let m := mGroup
  let γ := sLocalOrbitalDifferenceGenerator (F := F) (S := S) p ω
  have hgen (k : Fin _) : 1 < (m (γ k)).val := by
    have hN := sLocalOrbitalDifferenceGenerator_norm (F := F) (S := S) p ω k
    apply NNReal.coe_lt_coe.mp
    rw [NNReal.coe_one]
    change 1 < ((mₛ (γ k)).val : ℝ)
    rw [hN]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm (sLocalOrbitalActiveEquiv (F := F) (S := S) p ω k).val.val
  have hcomm :
      ∃ a : ℝ, 0 < a ∧ ∀ i, ∃ r : ℚ, Real.log ((m (γ i)).val : ℝ) = (r : ℝ) * a := by
    have hpN : (1 : ℝ) < p.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p
    refine ⟨_, Real.log_pos hpN, fun i ↦ ?_⟩
    let v := sLocalOrbitalActiveEquiv (F := F) (S := S) p ω i
    refine ⟨(v.val.val.asIdeal.inertiaDeg (𝓞 ℚ) : ℕ), ?_⟩
    change Real.log ((mₛ (sLocalOrbitalDifferenceGenerator (F := F) (S := S) p ω i)).val : ℝ) = _
    rw [sLocalOrbitalDifferenceGenerator_norm (F := F) (S := S) p ω i, Rat.cast_natCast]
    exact sLocalOrbitalPrimary_log_norm (F := F) (S := S) p v.val.val (Finset.mem_filter.mp v.property).2.1
  exact ⟨hgen, hcomm⟩

open Classical in
/-- The norm-weighted Fourier comparison identifies the primary and periodic quotients.
The change from a logarithmic moment to a Fourier jet is the reflection sign divided
by the total mass of the norm-one fiber. -/
private theorem sLocalOrbital_periodicFourierComparison (p : Vℚ) (ω : PontryaginDual J₁)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) (σ : ℕ ≃ Idx(p, ω))
    (hgen : ∀ k, 1 < (mGroup (sLocalOrbitalDifferenceGenerator (F := F) (S := S) p ω k)).val)
    (hcomm : ∃ a : ℝ, 0 < a ∧ ∀ i, ∃ r : ℚ,
      Real.log ((mGroup (sLocalOrbitalDifferenceGenerator (F := F) (S := S) p ω i)).val : ℝ) = (r : ℝ) * a) :
    let m := mGroup
    let hm := (sLocalOrbital_modulation (F := F) (S := S)).1
    let hs := (sLocalOrbital_modulation (F := F) (S := S)).2
    let γ := sLocalOrbitalDifferenceGenerator (F := F) (S := S) p ω
    let U := H₀(ω⁻¹) ⧸ (modulatedIsotypicDifferenceProduct m hm hs ω⁻¹ univ
      ordConnected_univ (mem_univ (0 : ℝ)) (List.ofFn γ)).range
    let d (j : ModelIndex(p, ω)) : StrongDual ℂ U :=
      modulatedQuotientLogMoment m hm hs ω⁻¹ γ hgen μorb j
    let mass : ℂ := (sLocalNormOneQuotientMeasure F S).real univ
    mass ≠ 0 ∧ ∃ (ι : ModelIndex(p, ω) ≃ Idx(p, ω)) (T : Q(p, ω) ≃L[ℂ] U),
      (∀ j, (ι j).val = ((circleToComplex).comp j.val.1⁻¹, j.val.2)) ∧
      ∀ j x, sLocalOrbitalFourierJet (ι j) x =
        (mass⁻¹ * (-1 : ℂ) ^ j.val.2) * d j (T (π(p, ω) x)) := by
  classical
  let m := mGroup
  let hm := (sLocalOrbital_modulation (F := F) (S := S)).1
  let hs := (sLocalOrbital_modulation (F := F) (S := S)).2
  let γ := sLocalOrbitalDifferenceGenerator (F := F) (S := S) p ω
  let Λ := List.ofFn γ
  let J := ModelIndex(p, ω)
  let idx := sLocalOrbitalModelIndex_equiv (F := F) (S := S) p ω
  let ι := idx.choose
  have hι := idx.choose_spec
  let σ₀ := σ.trans ι.symm
  have hΛgen : ∀ g ∈ Λ, 1 < (m g).val := by
    intro g hg
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact hgen k
  have hΛ : Λ ≠ [] := by
    have hj := lt_of_le_of_lt (Nat.zero_le _) ((σ₀ 0).property)
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hj
    intro h
    have hlen := congrArg List.length h
    simp [Λ, γ] at hlen
    have hk₀ := k.isLt
    simp [hlen] at hk₀
  let R₀ := (modulatedIsotypicDifferenceProduct m hm hs ω⁻¹ univ ordConnected_univ
    (mem_univ (0 : ℝ)) Λ).range
  let Rint := (modulatedIsotypicDifferenceProduct m hm hs ω⁻¹ I₋ ordConnected_Ioi hI₋ Λ).range
  let U := H₀(ω⁻¹) ⧸ R₀
  let d (j : J) : StrongDual ℂ U := modulatedQuotientLogMoment m hm hs ω⁻¹ γ hgen μorb j
  let hBasis := modulatedQuotientLogMoment_bases m hm hs ω⁻¹ γ hgen μorb hcomm σ₀
  have hb := hBasis.choose_spec.1
  let hComparison := sLocalOrbital_intervalQuotient (F := F) (S := S) ω⁻¹ Λ hΛ hΛgen
  let E := hComparison.choose
  have hE := hComparison.choose_spec
  let hFourier := sLocalOrbital_shiftedFourier (F := F) (S := S) ω
  let A := hFourier.choose
  have hA := hFourier.choose_spec
  let C : Θₛ(ω) →L[ℂ] U := E.symm.toContinuousLinearMap.comp (Rint.mkQL.comp A)
  have hC (x : Θₛ(ω)) : E (C x) = Rint.mkQ (A x) :=
    E.apply_symm_apply _
  have hCsurj : Surjective C := by
    intro u
    let v := (R₀.mkQ_surjective u).choose
    have hv := (R₀.mkQ_surjective u).choose_spec
    let g := (hE v).choose
    have hgv := (hE v).choose_spec.1
    have hEg := (hE v).choose_spec.2
    let v' : sLocalDecayIsotype univ ω⁻¹ := ⟨v.val,
      (sLocalOrbital_isotype_eq (F := F) (S := S) univ (mem_univ (0 : ℝ)) ω⁻¹) ▸ v.property⟩
    let hLift := primaryAllExponents_fourier_lift (F := F) (S := S) ω⁻¹ v'
    let f := hLift.choose
    have hf := hLift.choose_spec
    have hfg : A ((Kₛ(ω)).mkQ f) = g := by
      apply Subtype.ext
      apply Subtype.ext
      exact funext fun x ↦ (hA f x).trans ((hf x).trans (hgv x).symm)
    refine ⟨(Kₛ(ω)).mkQ f, E.injective ?_⟩
    exact (hC _).trans ((congrArg Rint.mkQ hfg).trans (hEg.symm.trans (congrArg E hv)))
  have hcoord (j : J) (x : Θₛ(ω)) :
      d j (C x) = sLocalOrbital_logMoment j.val.1 j.val.2 (A x).val.val := by
    let v := (R₀.mkQ_surjective (C x)).choose
    have hv := (R₀.mkQ_surjective (C x)).choose_spec
    let g := (hE v).choose
    have hgv := (hE v).choose_spec.1
    have hEg := (hE v).choose_spec.2
    have hmem : g - A x ∈ Rint :=
      (Submodule.Quotient.eq Rint).mp (hEg.symm.trans ((congrArg E hv).trans (hC x)))
    have hz := sLocalOrbital_logMoment_difference_zero (F := F) (S := S) p ω j (g - A x) hmem
    have hI : ∀ y : H₋(ω⁻¹), Integrable
        (fun u ↦ y.val.val u * (j.val.1 u : ℂ) * (logNorm u : ℂ)^j.val.2) μorb :=
      fun y ↦ primaryDecay_logMoment_integrable I₋ hI₋ (by constructor <;> norm_num)
        y.val j.val.1 j.val.2
    change (∫ u, (g.val.val u - (A x).val.val u) * (j.val.1 u : ℂ) *
      (logNorm u : ℂ)^j.val.2 ∂μorb) = 0 at hz
    simp_rw [sub_mul, integral_sub (hI g) (hI (A x)), sub_eq_zero] at hz
    have hcoeff : d j (R₀.mkQ v) = sLocalOrbital_logMoment j.val.1 j.val.2 v.val.val := rfl
    have hgcoord : sLocalOrbital_logMoment j.val.1 j.val.2 v.val.val =
        sLocalOrbital_logMoment j.val.1 j.val.2 g.val.val :=
      congrArg (sLocalOrbital_logMoment j.val.1 j.val.2) (funext hgv).symm
    exact (congrArg (d j) hv.symm).trans (hcoeff.trans (hgcoord.trans hz))
  let mass : ℂ := ((sLocalNormOneQuotientMeasure F S).real univ : ℂ)
  have hmass : mass ≠ 0 := by
    let : BorelSpace Kₛ := ⟨rfl⟩
    let : CompactSpace Kₛ := isCompact_iff_compactSpace.mp
      ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
    let : (sLocalNormOneQuotientMeasure F S).IsHaarMeasure :=
      (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
    exact Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := sLocalNormOneQuotientMeasure F S)).ne'
  let s (j : J) : ℂ := mass⁻¹ * (-1 : ℂ)^j.val.2
  have hsne (j : J) : s j ≠ 0 := mul_ne_zero (inv_ne_zero hmass) (pow_ne_zero _ (by norm_num))
  have hjet (j : J) (x : Θₛ(ω)) :
      sLocalOrbitalFourierJet (ι j) x = s j * d j (C x) := by
    let f := ((Kₛ(ω)).mkQ_surjective x).choose
    have hf := ((Kₛ(ω)).mkQ_surjective x).choose_spec
    have hy (g : Jₛ) : (A x).val.val g = (((mₛ g).val : ℝ) : ℂ) *
        sLocalHomogeneousAdelicThetaLinearMap F S ω⁻¹ (sAdeleSchwartzFourier f) g :=
      (congrArg (fun u : Θₛ(ω) ↦ (A u).val.val g) hf.symm).trans (hA f g)
    exact (congrArg (fun u : Θₛ(ω) ↦ sLocalOrbitalFourierJet (ι j) u) hf.symm).trans
      ((sLocalOrbital_shiftedFourierJet (F := F) (S := S) p ω j (ι j) (hι j) f (A x) hy).trans
        (congrArg (s j * ·) (hcoord j x).symm))
  have hF₁ := sLocalHomogeneousThetaSpace_frechet (F := F) (S := S) ω
  have hF₂ := (modulatedIsotypicDifferenceProduct_quotient.{_, 0} m hm hs ω⁻¹ Λ hΛgen).2.2
  let : TopologicalSpace.MetrizableSpace (Θₛ(ω)) := hF₁.choose_spec.2.1
  let : TopologicalSpace.MetrizableSpace U := hF₂.choose_spec.2.1
  let : IsTopologicalAddGroup U := hF₂.choose
  have hKer : C.ker = Rₚ(p, ω) :=
    orbitalQuotient_kernel_of_coefficients C (Rₚ(p, ω)) (fun i x ↦ sLocalOrbitalFourierJet i x)
      d ι s hsne (sLocalOrbitalFourierJet_commonKer (F := F) (S := S) p ω _hS _hp _hPic) hjet σ₀ _ hb
  have hOpen : IsOpenMap C :=
    isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hF₂)
      (X := fun _ ↦ Θₛ(ω)) (fun _ ↦ hF₁) (fun _ ↦ ContinuousLinearMap.id ℂ _)
      (fun _ ↦ Subset.rfl) (fun u ↦ ⟨0, u, rfl⟩) C hCsurj
  let hQuot := exists_quotient_equiv_of_kernel C
    (hOpen.isQuotientMap C.continuous hCsurj) (Rₚ(p, ω)) hKer
  let T := hQuot.choose
  have hT := hQuot.choose_spec
  refine ⟨hmass, ι, T, hι, fun j x ↦ ?_⟩
  exact (hjet j x).trans (congrArg (fun y : U ↦ s j * d j y) (hT x).symm)

/-- Paper: Theorem 7.3.1.6(2)–(3), p. 345.
Any enumeration of the Fourier functionals gives an unconditional basis of the strong dual.
With the same enumeration, its biorthogonal vectors are an absolute basis of the quotient. -/
theorem sLocalFourierOrbital_bases
    (p : Vℚ) (ω : PontryaginDual J₁)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) (σ : ℕ ≃ Idx(p, ω)) :
    ∃ (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω))) (ψ : Idx(p, ω) → Q(p, ω))
      (ev : ℕ → StrongDual ℂ (StrongDual ℂ (Q(p, ω)))),
      (∀ (n : ℕ) (ℓ : StrongDual ℂ (Q(p, ω))), ev n ℓ = ℓ (ψ (σ n))) ∧
      (∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
        sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x) ∧
      let e := ψ ∘ σ
      let d := D ∘ σ
      IsSchauderBasis d ev ∧ SchauderBasis.IsUnconditional d ev ∧
        IsSchauderBasis e d ∧ SchauderBasis.IsAbsolute e d := by
  classical
  let m := mGroup
  let hm := (sLocalOrbital_modulation (F := F) (S := S)).1
  let hs := (sLocalOrbital_modulation (F := F) (S := S)).2
  let γ := sLocalOrbitalDifferenceGenerator (F := F) (S := S) p ω
  let J := ModelIndex(p, ω)
  have hgen := (sLocalOrbitalDifferenceGenerator_periods p ω).1
  have hcomm := (sLocalOrbitalDifferenceGenerator_periods p ω).2
  let cmp := sLocalOrbital_periodicFourierComparison p ω _hS _hp _hPic σ hgen hcomm
  let ι := cmp.2.choose
  let T := cmp.2.choose_spec.choose
  have hjet := cmp.2.choose_spec.choose_spec.2
  let σ₀ := σ.trans ι.symm
  let U := H₀(ω⁻¹) ⧸ (modulatedIsotypicDifferenceProduct m hm hs ω⁻¹ univ
    ordConnected_univ (mem_univ (0 : ℝ)) (List.ofFn γ)).range
  let d (j : J) : StrongDual ℂ U := modulatedQuotientLogMoment m hm hs ω⁻¹ γ hgen μorb j
  let mass : ℂ := (sLocalNormOneQuotientMeasure F S).real univ
  let s (j : J) : ℂ := mass⁻¹ * (-1 : ℂ)^j.val.2
  have hsne (j : J) : s j ≠ 0 := mul_ne_zero (inv_ne_zero cmp.1) (pow_ne_zero _ (by norm_num))
  let hBasis := modulatedQuotientLogMoment_bases m hm hs ω⁻¹ γ hgen μorb hcomm σ₀
  let ψ₀ := hBasis.choose
  have hb := hBasis.choose_spec.1
  have ha := hBasis.choose_spec.2.1
  let D (j : Idx(p, ω)) : StrongDual ℂ (Q(p, ω)) :=
    s (ι.symm j) • (d (ι.symm j)).comp T.toContinuousLinearMap
  let ψ (j : Idx(p, ω)) : Q(p, ω) := (s (ι.symm j))⁻¹ • T.symm (ψ₀ (ι.symm j))
  let ev (n : ℕ) : StrongDual ℂ (StrongDual ℂ (Q(p, ω))) :=
    ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (ψ (σ n))
  refine ⟨D, ψ, ev, fun _ _ ↦ rfl, fun j x ↦ ?_, ?_⟩
  · exact (hjet (ι.symm j) x).symm.trans
      (congrArg (fun i ↦ sLocalOrbitalFourierJet i x) (ι.apply_symm_apply j))
  · have h := orbitalQuotient_rescale_basis T (ψ₀ ∘ σ₀) (d ∘ σ₀) hb ha
      (s ∘ σ₀) (fun n ↦ hsne (σ₀ n))
    exact sLocalOrbital_dual_of_absolute p ω _hS _hp _hPic (ψ ∘ σ) (D ∘ σ) h.1 h.2

/-- Rescale and transport a prescribed biorthogonal family and its seminorm. -/
private theorem orbitalQuotient_rescale_biorthogonal {I J E Q U : Type*}
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    [AddCommGroup U] [Module ℂ U] [TopologicalSpace U]
    (π : E → Q) (hπ : Surjective π) (ι : J ≃ I) (T : Q ≃L[ℂ] U)
    (s : J → ℂ) (hs : ∀ j, s j ≠ 0) (d : J → StrongDual ℂ U)
    (jet : I → E → ℂ) (hjet : ∀ j x, jet (ι j) x = s j * d j (T (π x)))
    (ψ : I → Q) [DecidableEq I] (hψ : ∀ i j x, π x = ψ j → jet i x = if i = j then 1 else 0)
    (q : Seminorm ℂ Q) (hq : Continuous q) :
    ∃ (η : J → U) (q' : Seminorm ℂ U), (∀ j, d j (η j) = 1) ∧
      (∀ i j, i ≠ j → d i (η j) = 0) ∧ Continuous q' ∧
      ∀ j, q' (η j) = ‖s j‖ * q (ψ (ι j)) := by
  classical
  let η (j : J) := s j • T (ψ (ι j))
  have coord (i j : J) : s i * d i (T (ψ (ι j))) = if i = j then 1 else 0 := by
    obtain ⟨x, hx⟩ := hπ (ψ (ι j))
    calc
      _ = s i * d i (T (π x)) := congrArg (fun y ↦ s i * d i (T y)) hx.symm
      _ = jet (ι i) x := (hjet i x).symm
      _ = _ := by simpa only [ι.apply_eq_iff_eq] using hψ (ι i) (ι j) x hx
  refine ⟨η, q.comp T.symm.toLinearMap, fun j ↦ ?_, fun i j hn ↦ ?_, hq.comp T.symm.continuous, fun j ↦ ?_⟩
  · simpa only [η, map_smul, smul_eq_mul, eq_self, ite_true] using coord j j
  · have h := coord i j
    simp only [hn, ↓reduceIte] at h
    simp [η, (mul_eq_zero.mp h).resolve_left (hs i)]
  · change q (T.symm (s j • T (ψ (ι j)))) = _
    rw [map_smul, T.symm_apply_apply, map_smul_eq_mul]

/-- Two character lattices agreeing at one point also agree after opposite integer shifts. -/
private theorem orbitalFourierLattice_reflect_shift {a b : Circle} (P l t u : ℝ) (m₀ n₀ n : ℤ)
    (h : a * Circle.exp (-((n₀ : ℝ) * P - t) * l) = b * Circle.exp (((m₀ : ℝ) * P - u) * l)) :
    a * Circle.exp (-((n : ℝ) * P - t) * l) =
      b * Circle.exp ((((m₀ + n₀ - n : ℤ) : ℝ) * P - u) * l) := by
  have h₀ := congrArg (· * Circle.exp (((n₀ : ℝ) - n) * P*l)) h
  simp only [mul_assoc, ← Circle.exp_add] at h₀
  convert h₀ using 3 <;> push_cast <;> ring

/-- The model index inverts the unitary character of an orbital lattice point. -/
private theorem sLocalOrbital_lattice_inverse_character (χ : PontryaginDual Jₛ) (v : S) (t : ℝ) (n : ℤ)
    (ξ : PontryaginDual Jₛ) (hξ : (circleToComplex).comp ξ⁻¹ = lattice(χ, v, t, n)) (x : Jₛ) :
    ξ x = (χ x)⁻¹ * Circle.exp (-((n : ℝ) * period(v) - t) * logNorm x) := by
  let b := (n : ℝ) * period(v) - t
  have hpos : 0 < ((mₛ x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have h := DFunLike.congr_fun hξ x
  change (((ξ x)⁻¹ : Circle) : ℂ) = (χ x : ℂ) * (((mₛ x).val : ℝ) : ℂ) ^ ((b : ℂ) * Complex.I) at h
  have hb : (((mₛ x).val : ℝ) : ℂ) ^ ((b : ℂ) * Complex.I) =
      (Circle.exp (b * logNorm x) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'), ← Complex.ofReal_log hpos.le,
      Circle.coe_exp]
    congr 1
    push_cast
    ring
  rw [hb] at h
  have he : (ξ x)⁻¹ = χ x * Circle.exp (b * logNorm x) := Circle.ext h
  have hi := congrArg Inv.inv he
  simpa only [inv_inv, mul_inv, ← Circle.exp_neg, neg_mul] using hi


open Classical in
/-- Reflection and translation of the lattice index preserve a fixed polynomial
degree, uniformly over all moment orders at that character. -/
private theorem sLocalOrbital_modelFrequency_growth (p : Vℚ) (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ)
    (v : S) (t : ℝ) (n₀ : ℤ) (j₀ : Idx(p, ω)) (hj₀ : j₀.val.1 = lattice(χ, v, t, n₀))
    (hv₀ : v ∈ sLocalFinitePolePlaces j₀.val.1)
    (k : Fin (Fintype.card (sLocalOrbitalActivePlaces p ω)))
    (hk : (sLocalOrbitalActiveEquiv p ω k).val = v)
    (ι : ModelIndex(p, ω) ≃ Idx(p, ω)) (hι : ∀ j, (ι j).val = ((circleToComplex).comp j.val.1⁻¹, j.val.2))
    (X : PontryaginDual Jₛ) (a : ℝ) (freq : ℤ → PontryaginDual Jₛ)
    (hf : ∀ n x, freq n x = X x * Circle.exp (((n : ℝ) * period(v) - a) * logNorm x))
    (hfr : range freq = modulatedCyclicAnnihilatorFiber mGroup ω⁻¹ (sLocalOrbitalDifferenceGenerator p ω k))
    (N : ModelIndex(p, ω) → ℝ) (e : ℕ) (B : ℝ) (hB : 0 < B)
    (hbound : ∀ (n : ℤ) j, j.val.1 = freq n → N j ≤ B * (1 + |(n : ℝ)|) ^ e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (j : Idx(p, ω)), j.val.1 = lattice(χ, v, t, n) →
      N (ι.symm j) ≤ C * (1 + |(n : ℝ)|) ^ e := by
  classical
  have hgen₀ := ((sLocalOrbitalFinitePole_iff ω v j₀.val.1 j₀.property.1).mp hv₀).2
  have hjc (j : Idx(p, ω)) :
      j.val.1 = (circleToComplex).comp (ι.symm j).val.1⁻¹ := by
    have hh := congrArg Prod.fst (hι (ι.symm j))
    exact (congrArg (fun z : Idx(p, ω) ↦ z.val.1) (ι.apply_symm_apply j).symm).trans hh
  have hmem : (ι.symm j₀).val.1 ∈ modulatedCyclicAnnihilatorFiber mGroup ω⁻¹ (sLocalOrbitalDifferenceGenerator p ω k) := by
    apply (mem_modulatedCyclicAnnihilatorFiber_iff mGroup ω⁻¹ (sLocalOrbitalDifferenceGenerator p ω k) _).mpr
    refine ⟨?_, sLocalOrbitalModelIndex_restrict p ω (ι.symm j₀)⟩
    change (ι.symm j₀).val.1 (sLocalOrbitalInsert (sLocalOrbitalActiveEquiv p ω k).val
      (sLocalOrbitalUniformizer (sLocalOrbitalActiveEquiv p ω k).val))⁻¹ = 1
    rw [hk, map_inv]
    apply Circle.ext
    rw [hjc j₀] at hgen₀
    exact hgen₀
  have hfound : ∃ m₀ : ℤ, freq m₀ = (ι.symm j₀).val.1 := Set.mem_range.mp (hfr.symm ▸ hmem)
  let m₀ := hfound.choose
  have hm₀ := hfound.choose_spec
  have hmodel (n : ℤ) (j : Idx(p, ω)) (hj : j.val.1 = lattice(χ, v, t, n)) :
      (ι.symm j).val.1 = freq (m₀ + n₀ - n) := by
    apply ContinuousMonoidHom.ext
    intro x
    have h₀ := sLocalOrbital_lattice_inverse_character χ v t n₀ (ι.symm j₀).val.1 ((hjc j₀).symm.trans hj₀) x
    have h := sLocalOrbital_lattice_inverse_character χ v t n (ι.symm j).val.1 ((hjc j).symm.trans hj) x
    have href := (DFunLike.congr_fun hm₀ x).trans h₀
    rw [hf] at href
    exact (h.trans (orbitalFourierLattice_reflect_shift _ _ _ _ m₀ n₀ n href.symm)).trans (hf _ _).symm
  let b : ℝ := |((m₀ + n₀ : ℤ) : ℝ)|
  have hcost (n : ℤ) : 1 + |((m₀ + n₀ - n : ℤ) : ℝ)| ≤ (1 + b) * (1 + |(n : ℝ)|) := by
    rw [Int.cast_sub]
    have hab := abs_sub (((m₀ + n₀ : ℤ) : ℝ)) (n : ℝ)
    change |(((m₀ + n₀ : ℤ) : ℝ)) - n| ≤ b + |(n : ℝ)| at hab
    nlinarith [mul_nonneg (show 0 ≤ b from abs_nonneg _) (abs_nonneg (n : ℝ))]
  have hbpos : 0 < 1 + b := by
    dsimp [b]
    positivity
  refine ⟨B * (1 + b) ^ e, by positivity, fun n j hj ↦ ?_⟩
  have h := hbound (m₀ + n₀ - n) (ι.symm j) (hmodel n j hj)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |((m₀ + n₀ - n : ℤ) : ℝ)|) (hcost n) e
  rw [mul_pow] at hpow
  exact (h.trans (mul_le_mul_of_nonneg_left hpow hB.le)).trans_eq (mul_assoc _ _ _).symm

open Classical in
/-- The periodic growth estimate transported across the norm-weighted Fourier comparison.
The Fourier normalization has constant norm on each primary pole block. -/
private theorem sLocalFourierOrbital_growth_of_periodic
    (p : Vℚ) (χ : PontryaginDual Jₛ) (ω : PontryaginDual J₁)
    (v : S) (t : ℝ)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial)
    (_hv : v.val ∈ Sₚ(p))
    (ψ : Idx(p, ω) → Q(p, ω))
    (_hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0)
    (q : Seminorm ℂ Q(p, ω)) (_hq : Continuous q) :
    ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℤ) (j : Idx(p, ω)), j.val.1 = lattice(χ, v, t, n) →
        v ∈ sLocalFinitePolePlaces (F := F) (S := S) j.val.1 → q (ψ j) ≤ C * (1 + |(n : ℝ)|) ^ d := by
  classical
  by_cases hex : ∃ (n : ℤ) (j : Idx(p, ω)), j.val.1 = lattice(χ, v, t, n) ∧ v ∈ sLocalFinitePolePlaces j.val.1
  swap
  · exact ⟨0, 1, one_pos, fun n j h hj ↦ (hex ⟨n, j, h, hj⟩).elim⟩
  obtain ⟨n₀, j₀, hj₀, hv₀⟩ := hex
  rcases sLocalOrbitalIndex_enumerable_or_empty (F := F) (S := S) p ω _hS _hp _hPic with hσ | ⟨hE, -⟩
  swap
  · exact (hE.false j₀).elim
  obtain ⟨σ⟩ := hσ
  let m := mGroup
  let hm := (sLocalOrbital_modulation (F := F) (S := S)).1
  let hs := (sLocalOrbital_modulation (F := F) (S := S)).2
  let γ := sLocalOrbitalDifferenceGenerator (F := F) (S := S) p ω
  let J := ModelIndex(p, ω)
  have hgen := (sLocalOrbitalDifferenceGenerator_periods p ω).1
  have hcomm := (sLocalOrbitalDifferenceGenerator_periods p ω).2
  let cmp := sLocalOrbital_periodicFourierComparison (F := F) (S := S) p ω _hS _hp _hPic σ hgen hcomm
  have hmass := cmp.1
  let ι := cmp.2.choose
  let T := cmp.2.choose_spec.choose
  have hι := cmp.2.choose_spec.choose_spec.1
  have hjet := cmp.2.choose_spec.choose_spec.2
  let mass : ℂ := (sLocalNormOneQuotientMeasure F S).real univ
  let s (j : J) : ℂ := mass⁻¹ * (-1 : ℂ) ^ j.val.2
  have hsne (j : J) : s j ≠ 0 := mul_ne_zero (inv_ne_zero hmass) (pow_ne_zero _ (by norm_num))
  let U := H₀(ω⁻¹) ⧸ (modulatedIsotypicDifferenceProduct m hm hs ω⁻¹ univ
    ordConnected_univ (mem_univ (0 : ℝ)) (List.ofFn γ)).range
  let d (j : J) : StrongDual ℂ U := modulatedQuotientLogMoment m hm hs ω⁻¹ γ hgen μorb j
  have hcoord (j : J) (x : Θₛ(ω)) : sLocalOrbitalFourierJet (ι j) x =
      s j * d j (T (π(p, ω) x)) := hjet j x
  let fam := orbitalQuotient_rescale_biorthogonal
    (π(p, ω)) (Rₚ(p, ω)).mkQ_surjective ι T s hsne d (fun i x ↦ sLocalOrbitalFourierJet i x)
    hcoord ψ _hψ q _hq
  let η := fam.choose
  let q' := fam.choose_spec.choose
  have diag := fam.choose_spec.choose_spec.1
  have off := fam.choose_spec.choose_spec.2.1
  have hq' := fam.choose_spec.choose_spec.2.2.1
  have hsemin := fam.choose_spec.choose_spec.2.2.2
  have semin (j : J) : q' (η j) = ‖mass⁻¹‖ * q (ψ (ι j)) := by
    have habs : ‖s j‖ = ‖mass⁻¹‖ := by
      change ‖mass⁻¹ * (-1 : ℂ) ^ j.val.2‖ = ‖mass⁻¹‖
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
    exact (hsemin j).trans (congrArg (fun a ↦ a * q (ψ (ι j))) habs)
  have hur := ((sLocalOrbitalFinitePole_iff (F := F) (S := S) ω v j₀.val.1 j₀.property.1).mp hv₀).1
  let av : sLocalOrbitalActivePlaces (F := F) (S := S) p ω := ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, _hv, hur⟩⟩
  let k := (sLocalOrbitalActiveEquiv (F := F) (S := S) p ω).symm av
  have hk : (sLocalOrbitalActiveEquiv (F := F) (S := S) p ω k).val = v :=
    congrArg Subtype.val ((sLocalOrbitalActiveEquiv (F := F) (S := S) p ω).apply_symm_apply av)
  have hL : Real.log ((m (γ k)).val : ℝ) = Real.log (v.val.asIdeal.absNorm : ℝ) := by
    change Real.log ((mₛ (sLocalOrbitalDifferenceGenerator (F := F) (S := S) p ω k)).val : ℝ) = _
    rw [sLocalOrbitalDifferenceGenerator_norm, hk]
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨X, _, _, hX, _⟩ := exists_modulatedCyclicCharacter_lifts m (γ k) τ hτ (hgen k)
  choose t₀ ht₀ using fun (i : Fin _) (η' : PontryaginDual m.toMonoidHom.ker) ↦
    (existsUnique_modulatedCharacterPhase m (γ i) (hgen i) (X η')).exists
  let bound := modulatedQuotientLogMoment_biorthogonal_growth m hm hs ω⁻¹ γ hgen X hX
    t₀ ht₀ μorb hcomm η diag off q' hq'
  let e := bound.choose
  let B := (bound.choose_spec k).choose
  have hB := (bound.choose_spec k).choose_spec.1
  have hbound := (bound.choose_spec k).choose_spec.2
  let freq (n : ℤ) : PontryaginDual Jₛ :=
    ((PontryaginDual.map (⟨QuotientGroup.mk' (Subgroup.zpowers (γ k)), QuotientGroup.continuous_mk⟩ :
      Jₛ →ₜ* (Jₛ ⧸ Subgroup.zpowers (γ k))) (modulatedCyclicCharacter m (γ k) (hgen k)
        X (t₀ k) (ht₀ k) (ω⁻¹, n))))⁻¹
  have hf (n : ℤ) (x : Jₛ) : freq n x = X ω⁻¹ x * Circle.exp (((n : ℝ) * period(v) - t₀ k ω⁻¹) * logNorm x) := by
    calc
      _ = X ω⁻¹ x * Circle.exp (-((t₀ k ω⁻¹ - 2 * Real.pi * (n : ℝ) / Real.log ((m (γ k)).val : ℝ)) *
            Real.log ((m x).val : ℝ))) := by
        change (modulatedCyclicCharacter m (γ k) (hgen k) X (t₀ k) (ht₀ k) (ω⁻¹, n)
          (QuotientGroup.mk x))⁻¹ = _
        rw [modulatedCyclicCharacter_mk, Circle.exp_neg, mul_inv, inv_inv]
      _ = _ := by
        rw [hL]
        congr 2
        change -((t₀ k ω⁻¹ - 2 * Real.pi * (n : ℝ) / Real.log (v.val.asIdeal.absNorm : ℝ)) *
          logNorm x) = ((n : ℝ) * period(v) - t₀ k ω⁻¹) * logNorm x
        ring
  have hfr := (modulatedPeriodicFrequency_bijective m hm hs ω⁻¹ γ hgen X hX t₀ ht₀ k).2
  change range freq = _ at hfr
  let hres := sLocalOrbital_modelFrequency_growth p ω χ v t n₀ j₀ hj₀ hv₀ k hk ι hι (X ω⁻¹) (t₀ k ω⁻¹)
    freq hf hfr (fun j ↦ q' (η j)) e B hB hbound
  let C := hres.choose
  have hC := hres.choose_spec.1
  have hscale := hres.choose_spec.2
  have hnorm : 0 < ‖mass⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hmass)
  refine ⟨e, C / ‖mass⁻¹‖, div_pos hC hnorm, fun n j hj _ ↦ ?_⟩
  have heq : ‖mass⁻¹‖ * q (ψ j) = q' (η (ι.symm j)) :=
    (congrArg (fun i : Idx(p, ω) ↦ ‖mass⁻¹‖ * q (ψ i)) (ι.apply_symm_apply j).symm).trans (semin _).symm
  have h := heq.le.trans (hscale n j hj)
  calc
    q (ψ j) ≤ (C * (1 + |(n : ℝ)|) ^ e) / ‖mass⁻¹‖ := (le_div_iff₀ hnorm).mpr (by simpa only [mul_comm (q (ψ j))] using h)
    _ = _ := by ring

end PrimaryBases

local notation "restrict₁(" χ ")" => ((χ : PontryaginDual Jₛ).comp
  (⟨(mₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ))

section LatticeEstimates

open Classical in
/-- Paper: Theorem 7.3.1.6(4), p. 345.
The seminorm of a biorthogonal Fourier vector grows at most polynomially along a
local pole lattice, uniformly over the derivative orders at each pole.
Deviation: A constant times a power of one plus the index norm expresses the polynomial bound.
The finite initial segment is absorbed into the constant. -/
theorem sLocalFourierOrbital_biorthogonal_growth
    (p : Vℚ) (χ : PontryaginDual Jₛ) (ω : PontryaginDual J₁)
    (v : S) (u : (v.val.adicCompletion F)ˣ) (t : ℝ)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial)
    (_hω : ω = restrict₁(χ))
    (_hv : v.val ∈ Sₚ(p)) (_hu : uniformizerNorm(v, u)) (_ht : phase(χ, v, u, t))
    (ψ : Idx(p, ω) → Q(p, ω))
    (_hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0)
    (q : Seminorm ℂ Q(p, ω)) (_hq : Continuous q) :
    ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℤ) (j : Idx(p, ω)), j.val.1 = lattice(χ, v, t, n) →
        v ∈ sLocalFinitePolePlaces (F := F) (S := S) j.val.1 → q (ψ j) ≤ C * (1 + |(n : ℝ)|) ^ d :=
  sLocalFourierOrbital_growth_of_periodic p χ ω v t _hS _hp _hPic _hv ψ _hψ q _hq

/-- Uniform vertical decay restricts to rapid decay on an affine lattice. -/
private theorem sLocalOrbitalFourierJet_lattice_schwartz_rapidSamples (G : ℂ → ℂ)
    (hG : UniformlySchwartzOnStrip G (1/2) (3/2))
    (t d : ℝ) (hd : 0 < d) (N : ℕ) :
    ∃ C > (0 : ℝ), ∀ n : ℤ, ‖G (1 + ((t - n * d : ℝ) : ℂ) * Complex.I)‖ ≤
      C / (1 + |(n : ℝ)|) ^ N := by
  obtain ⟨C, hC, ht⟩ := hG.2.2 (1/4) (by norm_num) (by norm_num) (N+1) (by omega)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp ht)
  let A := max 1 T
  let g (y : ℝ) := G (1 + (y : ℂ) * Complex.I)
  have hg : Continuous g := by
    apply hG.2.1.continuousOn.comp_continuous (by fun_prop)
    intro y
    change 1 / 2 < (1 + (y : ℂ) * Complex.I).re ∧ (1 + (y : ℂ) * Complex.I).re < 3 / 2
    norm_num
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -A) (b := A)).bddAbove_image
    (f := fun y : ℝ ↦ (1 + |y|)^N * ‖g y‖) (by fun_prop)
  let K := max (max B (2 ^ N * C)) 1
  have hK : 0 < K := zero_lt_one.trans_le (le_max_right _ _)
  have bound (y : ℝ) : (1 + |y|)^N * ‖g y‖ ≤ K := by
    by_cases hy : |y| ≤ A
    · exact (hB ⟨y, abs_le.mp hy, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
    have h1 : 1 ≤ |y| := (le_max_left _ _).trans (le_of_not_ge hy)
    have hp : 0 < |y| := zero_lt_one.trans_le h1
    have hh := hT |y| ((le_max_right _ _).trans (le_of_not_ge hy)) y rfl 1 (by norm_num)
    change ‖g y‖ ≤ C / |y| ^ (N+1) at hh
    have hm := (le_div_iff₀ (pow_pos hp _)).mp hh
    have hn : |y| ^ N ≤ |y| ^ (N+1) := pow_le_pow_right₀ h1 (by omega)
    calc
      (1 + |y|)^N * ‖g y‖ ≤ (2 * |y|)^N * ‖g y‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) _) (norm_nonneg _)
      _ = 2^N * (|y| ^ N * ‖g y‖) := by rw [mul_pow]; ring
      _ ≤ 2^N * C := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans (by simpa only [mul_comm ‖g y‖] using hm)
      _ ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  let M := (1 + |t| + d) / d
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M^N * K, mul_pos (pow_pos hM _) hK, fun n ↦ ?_⟩
  let y := t - (n : ℝ) * d
  have htri : |(n : ℝ)| * d ≤ |t| + |y| := by
    rw [← abs_of_pos hd, ← abs_mul]
    simpa [y] using (abs_sub t y)
  have hscale : 1 + |(n : ℝ)| ≤ M * (1 + |y|) := by
    dsimp [M]
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    nlinarith [abs_nonneg t, abs_nonneg y, mul_nonneg (abs_nonneg t) (abs_nonneg y),
      mul_nonneg hd.le (abs_nonneg y)]
  apply (le_div_iff₀ (by positivity)).2
  change ‖g y‖ * (1 + |(n : ℝ)|)^N ≤ _
  calc
    _ ≤ ‖g y‖ * (M * (1 + |y|))^N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hscale _) (norm_nonneg _)
    _ = M^N * ((1 + |y|)^N * ‖g y‖) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (bound y) (pow_pos hM _).le

open Classical in
/-- Helper for `sLocalOrbitalFourierJet_lattice_schwartz`.
Paper: Theorem 7.3.1.6(5), p. 345.
Scalar form of the rapid decay: the Fourier jet value at a fixed order, along the local
pole lattice through the chosen phase, is bounded by an arbitrary negative power of
`1 + |n|`. The paper only alludes to this estimate, on p. 361, as following from the
exponential decay of the Mellin transforms of the tests; it is what makes the sequence
Schwartz.
Deviation: The sequence is extended by zero where the place is not a pole of `c` or the
order is outside the primary multiplicity, as in the statement. -/
private theorem sLocalOrbitalFourierJet_lattice_schwartz_valueDecay
    (p : Vℚ) (χ : PontryaginDual Jₛ) (v : S) (u : (v.val.adicCompletion F)ˣ) (t : ℝ)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial)
    (_hv : v.val ∈ Sₚ(p)) (_hu : uniformizerNorm(v, u)) (_ht : phase(χ, v, u, t))
    (f : ℬₛ) (k N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ,
      ‖(if v ∈ sLocalFinitePolePlaces (F := F) (S := S) (lattice(χ, v, t, n)) ∧
          k < sLocalPrimaryPoleMultiplicity (F := F) (S := S) p (lattice(χ, v, t, n)) then
          iteratedDeriv k (fourierZeta(lattice(χ, v, t, n)) f) 0
        else 0)‖ ≤ C / (1 + |(n : ℝ)|) ^ N := by
  let Z (s : ℂ) := sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) s)
  have hd : 0 < period(v) := div_pos (by positivity) (Real.log_pos (by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val))
  have hs : UniformlySchwartzOnStrip (iteratedDeriv k Z) (1/2) (3/2) :=
    sLocalIdelicZFunction_schwartzOnStrip (sAdeleSchwartzFourier f) χ⁻¹ _ _ (by norm_num) (by norm_num) k
  obtain ⟨C, hC, h⟩ := sLocalOrbitalFourierJet_lattice_schwartz_rapidSamples (iteratedDeriv k Z) hs t _ hd N
  refine ⟨C, hC, fun n ↦ ?_⟩
  split_ifs
  · let a : ℂ := (((n : ℝ) * period(v) - t : ℝ) : ℂ) * Complex.I
    have he : fourierZeta(lattice(χ, v, t, n)) f = fun z ↦ Z ((1 - a) - z) := by
      funext z
      simp only [normTwist_normTwist, sLocal_dual_normTwist]
      dsimp only [Z, a]
      congr 2
      ring
    simp only [he, iteratedDeriv_comp_const_sub, sub_zero, norm_smul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul]
    convert h n using 3
    dsimp [a]
    push_cast
    ring
  · simp only [norm_zero]
    positivity

open scoped ENNReal in
/-- A sequence with all inverse-power bounds defines an elementary Schwartz test on the integer lattice. -/
private theorem sLocalOrbitalFourierJet_lattice_schwartz_rapidSequence (g : ℤ → ℂ)
    (hg : ∀ N : ℕ, ∃ C > (0 : ℝ), ∀ n : ℤ, ‖g n‖ ≤ C / (1 + |(n : ℝ)|)^N) :
    ∃ s : RapidDecaySequence 1, ∀ n : ℤ, s (fun _ ↦ n) = g n := by
  let e := (Equiv.funUnique (Fin 1) ℤ).symm
  have hbase : Summable (fun n : ℤ ↦ 1 / (1 + |(n : ℝ)|)^2) := by
    have hn := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
    apply Summable.of_nat_of_neg
    · simpa [abs_of_nonneg, add_comm] using hn
    · simpa [abs_of_nonneg, add_comm] using hn
  let f (a : Fin 1 → ℤ) := g (a 0)
  have hs (j : ℕ) : Summable (fun n : ℤ ↦ (1 + |(n : ℝ)|)^j * ‖g n‖) := by
    obtain ⟨C, hC, hb⟩ := hg (j+2)
    apply (hbase.mul_left C).of_nonneg_of_le (fun _ ↦ by positivity)
    intro n
    have hn : 0 < 1 + |(n : ℝ)| := by positivity
    calc
      _ ≤ (1 + |(n : ℝ)|)^j * (C / (1 + |(n : ℝ)|)^(j+2)) :=
        mul_le_mul_of_nonneg_left (hb _) (pow_pos hn _).le
      _ = _ := by rw [pow_add]; field_simp
  refine ⟨⟨f, fun j ↦ ?_⟩, fun _ ↦ rfl⟩
  rw [rapidDecaySequenceBound, ← e.tsum_eq]
  have he (n : ℤ) : ‖(WithLp.toLp 2 (fun i ↦ ((e n i : ℤ) : ℝ)) : EuclideanSpace ℝ (Fin 1))‖ =
      |(n : ℝ)| := by simp [e, EuclideanSpace.norm_eq, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
  calc
    _ = ∑' n : ℤ, ENNReal.ofReal ((1 + |(n : ℝ)|)^j * ‖g n‖) := by
      apply tsum_congr
      intro n
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one, ofReal_norm]
      congr 2
      apply congrArg (fun q : ℝ≥0∞ ↦ 1 + q)
      exact (ofReal_norm _).symm.trans (congrArg ENNReal.ofReal (he n))
    _ < ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) (hs j)]
      exact ENNReal.ofReal_lt_top

/-- Helper for `sLocalOrbitalFourierJet_lattice_schwartz`.
A complex sequence on the integer lattice that decays faster than every reciprocal power is
the restriction of a Schwartz-Bruhat function on the integers. This carries no analytic
input: the rapid decay of the coefficients is the whole hypothesis. -/
private theorem sLocalOrbitalFourierJet_lattice_schwartz_bridge (g : ℤ → ℂ)
    (hg : ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ, ‖g n‖ ≤ C / (1 + |(n : ℝ)|) ^ N) :
    ∃ a : SchwartzBruhat (Multiplicative ℤ), ∀ n : ℤ, a (Multiplicative.ofAdd n) = g n := by
  obtain ⟨s, hs⟩ := sLocalOrbitalFourierJet_lattice_schwartz_rapidSequence g hg

  let H := Multiplicative ℤ
  let E₀ := ElementaryLieGroup 0 0 1 PUnit
  let c : H ≃ₜ* Multiplicative E₀ :=
    { toFun := fun n ↦ Multiplicative.ofAdd (0, 0, fun _ ↦ n.toAdd, 0)
      invFun := fun x ↦ Multiplicative.ofAdd (x.toAdd.2.2.1 0)
      left_inv := fun _ ↦ rfl
      right_inv := fun x ↦ by
        apply Multiplicative.toAdd.injective
        apply Prod.ext (Subsingleton.elim _ _)
        apply Prod.ext (Subsingleton.elim _ _)
        apply Prod.ext _ (Subsingleton.elim _ _)
        exact funext fun i ↦ congrArg x.toAdd.2.2.1 (Subsingleton.elim 0 i)
      map_mul' := fun _ _ ↦ by
        apply Multiplicative.toAdd.injective
        apply Prod.ext (Subsingleton.elim _ _)
        apply Prod.ext (Subsingleton.elim _ _)
        exact Prod.ext rfl (Subsingleton.elim _ _)
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  let p : ElementaryLCAPresentation H := ⟨0, 0, 1, PUnit, c⟩
  have hG := (lca_elementary_iff (G := H)).mpr ⟨p⟩
  let top : (⊤ : Subgroup H) ≃ₜ* H := ⟨Subgroup.topEquiv, continuous_subtype_val, continuous_id.subtype_mk _⟩
  let a : BruhatStructuralPair H := ⟨(⊤, OrderDual.toDual ⊥), isOpen_univ,
    isCompactlyGeneratedGroup_of_continuousMulEquiv top.symm hG.1,
    isBruhatGoodSubgroup_bot_iff.mpr hG.2, bot_le⟩
  let q : a.quotient ≃* H :=
    QuotientGroup.quotientKerEquivOfRightInverse a.val.1.subtype top.symm (fun _ ↦ rfl)
  let q' : a.quotient ≃ₜ* H :=
    { q with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr continuous_subtype_val
      continuous_invFun := QuotientGroup.continuous_mk.comp top.symm.continuous }
  let e : ElementaryLCAPresentation a.quotient := ⟨0, 0, 1, PUnit, q'.trans c⟩
  obtain ⟨E, hE⟩ := rapidDecaySequence_equiv_elementarySchwartz (r := 1)
  refine ⟨schwartzBruhatStageInclusion a e (E s), fun n ↦ ?_⟩
  change schwartzBruhatStageRealization a e (E s) (Multiplicative.ofAdd n) = _
  rw [schwartzBruhatStageRealization_apply, dite_eq_left (Subgroup.mem_top _)]
  exact (hE s _).trans (hs n)

open Classical in
/-- Paper: Theorem 7.3.1.6(5), p. 345.
The Fourier jet of each test at fixed order gives a Schwartz sequence along a local
pole lattice.
Deviation: The sequence is extended by zero where the place does not contribute
a pole or the derivative order is outside the primary multiplicity. -/
theorem sLocalOrbitalFourierJet_lattice_schwartz
    (p : Vℚ) (χ : PontryaginDual Jₛ) (v : S) (u : (v.val.adicCompletion F)ˣ) (t : ℝ)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial)
    (_hv : v.val ∈ Sₚ(p)) (_hu : uniformizerNorm(v, u)) (_ht : phase(χ, v, u, t))
    (f : ℬₛ) (k : ℕ) :
    ∃ a : SchwartzBruhat (Multiplicative ℤ), ∀ n : ℤ,
      let c := lattice(χ, v, t, n)
      a (Multiplicative.ofAdd n) =
        if v ∈ sLocalFinitePolePlaces (F := F) (S := S) c ∧
          k < sLocalPrimaryPoleMultiplicity (F := F) (S := S) p c then
          iteratedDeriv k (fourierZeta(c) f) 0
        else 0 := by
  obtain ⟨a, ha⟩ := sLocalOrbitalFourierJet_lattice_schwartz_bridge
    (fun n : ℤ ↦ if v ∈ sLocalFinitePolePlaces (F := F) (S := S) (lattice(χ, v, t, n)) ∧
        k < sLocalPrimaryPoleMultiplicity (F := F) (S := S) p (lattice(χ, v, t, n)) then
        iteratedDeriv k (fourierZeta(lattice(χ, v, t, n)) f) 0
      else 0)
    (fun N ↦ sLocalOrbitalFourierJet_lattice_schwartz_valueDecay
      (F := F) (S := S) p χ v u t _hS _hp _hPic _hv _hu _ht f k N)
  exact ⟨a, fun n ↦ ha n⟩

end LatticeEstimates

section PolarLaurentBases

local notation "rhoCoeff(" c ", " r ")" =>
  complexResidue (fun z : ℂ ↦ sLocalRhoFactor (twistₛ (c) z) *
    z ^ ((sLocalRhoPoleOrder (c) : ℤ) - ((r : ℕ) : ℤ) - 1)) 0

/-- The union of the pole lattices has finite multiplicity. An inverse-square bound on
each lattice therefore implies summability over all the selected centers and jet orders. -/
private theorem sLocalPolarOrbital_bases_of_laurent_bounds_lattices
    (p : Vℚ) (ω : PontryaginDual J₁) (a : Idx(p, ω) → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (hlattice : ∀ (χ : PontryaginDual Jₛ) (v : S) (u : (v.val.adicCompletion F)ˣ) (t : ℝ),
      uniformizerNorm(v, u) → phase(χ, v, u, t) → ∃ C : ℝ, 0 ≤ C ∧
        ∀ (j : Idx(p, ω)) (n : ℤ), j.val.1 = lattice(χ, v, t, n) →
          v ∈ sLocalFinitePolePlaces (F := F) (S := S) j.val.1 → v.val ∈ Sₚ(p) →
            a j ≤ C / (1 + |(n : ℝ)|) ^ 2) : Summable a := by
  classical
  obtain ⟨χ, -, hcover⟩ := sLocalOrbitalIndex_enumerable_or_empty_chart ω
  choose u hu using (sLocalOrbitalIndex_enumerable_or_empty_uniformizer (F := F) (S := S))
  choose t ht using fun v : S ↦ (existsUnique_sLocalOrbitalPhase χ v (u v) (hu v)).exists
  choose C hC hbound using fun v : S ↦ hlattice χ v (u v) (t v) (hu v) (ht v)
  have locate (j : Idx(p, ω)) : ∃ (v : S) (n : ℤ), j.val.1 = lattice(χ, v, t v, n) ∧
      v ∈ sLocalFinitePolePlaces (F := F) (S := S) j.val.1 ∧ v.val ∈ Sₚ(p) := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) j.property.2)
    obtain ⟨s, hs⟩ := hcover j.val.1 j.property.1
    obtain ⟨n, hn⟩ := (existsUnique_sLocalOrbitalLatticeIndex χ v (u v) (hu v)
      (t v) (ht v) j.val.1 ⟨s, hs.symm⟩ (Finset.mem_filter.mp hv).1).exists
    exact ⟨v, n, hn, Finset.mem_filter.mp hv⟩
  choose v n hcenter hplace hprimary using locate
  let order (j : Idx(p, ω)) : Fin (Fintype.card S) :=
    ⟨j.val.2, j.property.2.trans_le (Finset.card_le_univ _)⟩
  let ι (j : Idx(p, ω)) : (S × Fin (Fintype.card S)) × ℤ := ((v j, order j), n j)
  have hinj : Injective ι := by
    intro j k hjk
    have hv : v j = v k := congrArg (fun i ↦ i.1.1) hjk
    have ho : order j = order k := congrArg (fun i ↦ i.1.2) hjk
    have hn : n j = n k := congrArg Prod.snd hjk
    apply Subtype.ext
    apply Prod.ext _ (congrArg Fin.val ho)
    rw [hcenter j, hcenter k, hv, hn]
  let g (i : (S × Fin (Fintype.card S)) × ℤ) := C i.1.1 / (1 + |(i.2 : ℝ)|) ^ 2
  have hz : Summable (fun n : ℤ ↦ 1 / (1 + |(n : ℝ)|) ^ 2) := by
    apply Summable.of_nat_of_neg
    all_goals
      simpa only [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast, add_comm (1 : ℝ), Nat.cast_add_one]
        using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  have hg : Summable g := by
    refine (summable_prod_of_nonneg (f := g) (fun i ↦ div_nonneg (hC i.1.1) (sq_nonneg _))).mpr
      ⟨fun i ↦ ?_, Summable.of_finite⟩
    simpa only [g, mul_one_div] using hz.mul_left (C i.1)
  exact (hg.comp_injective hinj).of_nonneg_of_le ha (fun j ↦
    hbound (v j) j (n j) (hcenter j) (hplace j) (hprimary j))

/-- Residues only depend on the germ on a punctured neighbourhood. -/
private theorem orbitalPolar_residue_congr {g h : ℂ → ℂ}
    (he : g =ᶠ[𝓝[≠] (0 : ℂ)] h) : complexResidue g 0 = complexResidue h 0 := by
  obtain ⟨δ, hδ, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he
  unfold complexResidue limUnder
  refine congrArg lim (Filter.map_congr ?_)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  rw [circleIntegral.integral_congr hr.1.le fun z hz ↦ hEq ⟨?_, ?_⟩]
  · rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
    exact hr.2
  · rintro rfl
    exact hr.1.ne (by simpa using hz)

/-- Unnormalized functional equation in a unitary norm chart. -/
private theorem orbitalPolar_fourier_eq (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    (fun z ↦ sLocalIdelicZFunction f (chart(χ) z)) =ᶠ[codiscrete ℂ]
      (fun z ↦ sLocalRhoFactor (chart(χ) z) * sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (chart(χ) z))) := by
  let Z (g : ℬₛ) (η : PontryaginDual Jₛ) (z : ℂ) := sLocalIdelicZFunction g (chart(η) z)
  let R (z : ℂ) := sLocalRhoFactor (chart(χ) z)
  let D (z : ℂ) := Z (sAdeleSchwartzFourier f) χ⁻¹ (1 - z)
  have hZ (g : ℬₛ) (η : PontryaginDual Jₛ) (z : ℂ) : MeromorphicAt (Z g η) z :=
    ((sLocalIdelicZFunction_meromorphic g η) (mem_univ z)).meromorphicAt
  have hEq : Z f χ =ᶠ[codiscrete ℂ] R * D := by
    apply sLocal_meromorphic_identity (hZ f χ) (fun z ↦ (sLocalRhoFactor_meromorphic χ z).mul
      ((hZ _ _ (1 - z)).comp_analyticAt (analyticAt_const.sub analyticAt_id)))
    intro z hz
    have hd : 0 < (1 - z).re := by simp; linarith [hz.2]
    change sLocalIdelicZFunction f (chart(χ) z) =
      R z * sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chart(χ⁻¹) (1 - z))
    refine (sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz.1, rfl⟩).trans ?_
    refine (sLocalIdelicZetaIntegral_functionalEquation f χ z hz).trans ?_
    refine (congrArg (fun c ↦ R z * sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) c)
      (sLocal_dual_normTwist χ z)).trans ?_
    exact congrArg (R z * ·)
      (sLocalIdelicZFunction_eq_integral (sAdeleSchwartzFourier f) ⟨χ⁻¹, 1 - z, hd, rfl⟩).symm
  filter_upwards [hEq] with z hz
  change Z f χ z = R z * D z at hz
  rw [sLocal_dual_normTwist]
  exact hz

/-- The top polar coefficient uses the same centered Laurent scale as all the other rows. -/
private theorem orbitalPolar_leading {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) (f : ℬₛ) :
    rhoCoeff(j.val.1, 0) ≠ 0 ∧
    sLocalPrincipalPartCoeff j.val.1 (sLocalRhoPoleOrder j.val.1) f =
      rhoCoeff(j.val.1, 0) * fourierZeta(j.val.1) f 0 := by
  classical
  let c := j.val.1
  let m := sLocalRhoPoleOrder c
  let ρ (z : ℂ) := sLocalRhoFactor (twistₛ c z)
  let H := fourierZeta(c) f
  have hm : 0 < m := by
    have hb : sLocalFinitePoleMultiplicity T c ≤ m := by
      dsimp [m]
      rw [sLocalRhoPoleOrder_eq_card_polePlaces]
      exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
    exact (Nat.zero_le _).trans_lt (j.property.2.trans_le hb)
  have hord : meromorphicOrderAt ρ 0 = ((-(m : ℤ) : ℤ) : WithTop ℤ) := by
    have ht := sLocalIdelicOrderBound_eq_neg_poleOrder c
    change min 0 (meromorphicOrderAt ρ 0) = _ at ht
    have hn : ((-(m : ℤ) : ℤ) : WithTop ℤ) < 0 := by exact_mod_cast (show -(m : ℤ) < 0 by omega)
    have hlt := (min_lt_iff.mp (ht.trans_lt hn)).resolve_left (lt_irrefl _)
    exact (min_eq_right hlt.le).symm.trans ht
  obtain ⟨χ, a, hc⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  have shift (z : ℂ) : twistₛ c z = chart(χ) (z + a) := by
    rw [← hc, normTwist_normTwist]
  have hρ : MeromorphicAt ρ 0 := by
    have heq : ρ = (fun u ↦ sLocalRhoFactor (chart(χ) u)) ∘ (fun z ↦ z+a) :=
      funext fun z ↦ congrArg sLocalRhoFactor (shift z)
    rw [heq]
    exact (sLocalRhoFactor_meromorphic χ _).comp_analyticAt (by fun_prop)
  obtain ⟨A, hA, hA0, hrep⟩ := (meromorphicOrderAt_eq_int_iff hρ).mp hord
  have hr (z : ℂ) (hz : z ≠ 0) (h : ρ z = (z - 0) ^ (-(m : ℤ)) • A z) :
      ρ z * z ^ ((m : ℤ) - 0 - 1) = A z / (z - 0) := by
    simp only [h, sub_zero, smul_eq_mul]
    rw [mul_right_comm, ← zpow_add₀ hz, show -(m : ℤ) + ((m : ℤ) - 1) = -1 by ring]
    simp [div_eq_mul_inv, mul_comm]
  have hc0 : rhoCoeff(c, 0) = A 0 := by
    apply Eq.trans (orbitalPolar_residue_congr (h := fun z ↦ A z / (z - 0)) ?_) (complexResidue_div_sub hA)
    filter_upwards [hrep, self_mem_nhdsWithin] with z hz hn
    exact hr z hn hz
  refine ⟨hc0.trans_ne hA0, ?_⟩
  change complexResidue (fun z ↦ sLocalIdelicZFunction f (twistₛ c z) / z ^ (-(m : ℤ)+1)) 0 = _
  have ht : Tendsto (fun z : ℂ ↦ z+a) (𝓝[≠] 0) (𝓝[≠] (0+a)) :=
    ((Homeomorph.addRight a).map_punctured_nhds_eq 0).le
  have hH : AnalyticAt ℂ H 0 := sLocalOrbitalFourierZeta_analyticAt j f
  refine (orbitalPolar_residue_congr (h := fun z ↦ (A z * H z) / (z - 0)) ?_).trans
    ((complexResidue_div_sub (g := fun z ↦ A z * H z) (hA.mul hH)).trans (congrArg (· * H 0) hc0.symm))
  filter_upwards [ht.eventually (nhdsNE_le_codiscrete _ (orbitalPolar_fourier_eq χ f)), hrep,
    self_mem_nhdsWithin] with z he ha hn
  have hn' : z ≠ 0 := hn
  have heq : sLocalIdelicZFunction f (twistₛ c z) = ρ z * H z := by
    simpa only [ρ, H, shift] using he
  rw [heq, ha]
  simp only [sub_zero, smul_eq_mul, zpow_add₀ hn', zpow_one, zpow_neg, zpow_natCast]
  field_simp [hn']


/-- At offset r, the polar coordinate is the convolution of the correcting Laurent
coefficients with the first r Taylor coefficients of the reflected Fourier test. -/
private theorem orbitalPolar_row {T : Finset V} {ω : PontryaginDual J₁}
    (j : I(T, ω)) (f : ℬₛ) :
    sLocalOrbitalPrincipalPart j ((Kₛ(ω)).mkQ f) =
      ∑ k ∈ Finset.range (j.val.2 + 1), rhoCoeff(j.val.1, k) *
        (iteratedDeriv (j.val.2 - k) (fourierZeta(j.val.1) f) 0 / ((j.val.2 - k).factorial : ℂ)) := by
  classical
  have hmult : sLocalFinitePoleMultiplicity T j.val.1 ≤ sLocalRhoPoleOrder j.val.1 := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces]
    exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
  have hbound := j.property.2.trans_le hmult
  change sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 _ ((Kₛ(ω)).mkQL f) = _
  rw [sLocalThetaPrincipalPartCoeff_mk, ← sLocalPrincipalPartCoeff_apply]
  by_cases hj : j.val.2 = 0
  · simpa [hj] using (orbitalPolar_leading j f).2
  · have he := sLocalPrincipalPartCoeff_lower_formula j.val.1 f (sLocalRhoPoleOrder j.val.1 - j.val.2)
      (by omega)
    simpa only [show sLocalRhoPoleOrder j.val.1 - (sLocalRhoPoleOrder j.val.1 - j.val.2) = j.val.2
      by omega] using he

section

open Finset

/-- Back substitution in a finite triangular block with a common leading scale. -/
private theorem finiteBlock_inverse_bound
    (m : ℕ) (w : ℕ → ℝ) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (h : ∀ r < m, w r ≤ A + H * ∑ s ∈ (range m).filter (r < ·), w s) :
    ∀ r < m, w r ≤ A * (1 + m * H) ^ (m - 1 - r) := by
  let B : ℝ := 1 + m * H
  have hB : 1 ≤ B := by dsimp [B]; exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hH)
  have step (k : ℕ) : ∀ r < m, m - 1 - r = k → w r ≤ A * B ^ k := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro r hr he
      by_cases hk : k = 0
      · rw [hk]
        have hempty : (range m).filter (r < ·) = ∅ := by
          ext s
          simp only [mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
          omega
        simpa [hempty] using h r hr
      have hk' : k - 1 < k := by omega
      have hP : 1 ≤ B ^ (k - 1) := one_le_pow₀ hB
      have hAP : A ≤ A * B ^ (k - 1) := by nlinarith
      have hsum : ∑ s ∈ (range m).filter (r < ·), w s ≤ (m : ℝ) * (A * B ^ (k - 1)) := by
        calc
          _ ≤ ∑ _s ∈ (range m).filter (r < ·), A * B ^ (k - 1) := by
            refine sum_le_sum fun s hs ↦ ?_
            obtain ⟨hs', hrs⟩ := mem_filter.mp hs
            have hsm := Finset.mem_range.mp hs'
            exact (ih (m - 1 - s) (by omega) s hsm rfl).trans
              (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (by omega)) hA)
          _ ≤ _ := by
            simp only [sum_const, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast (card_filter_le (range m) (r < ·)).trans_eq (card_range m)) (by positivity)
      calc
        w r ≤ _ := h r hr
        _ ≤ A * B ^ (k - 1) + H * ((m : ℝ) * (A * B ^ (k - 1))) :=
          add_le_add hAP (mul_le_mul_of_nonneg_left hsum hH)
        _ = A * B ^ k := by
          conv_rhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
          dsimp [B]
          ring
  exact fun r hr ↦ step (m - 1 - r) r hr rfl

/-- The common leading coefficient remains on the left, so the inverse requires bounds
only on the off-diagonal ratios, even when the leading coefficient varies with the center. -/
private theorem finiteBlock_biorthogonal_bound {E : Type*} [AddCommGroup E] [Module ℂ E]
    (q : Seminorm ℂ E) (m : ℕ) (a : ℕ → ℂ) (ψ η : ℕ → E)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hη : ∀ r < m, q (η r) ≤ A)
    (ha : ∀ k < m, k ≠ 0 → ‖a k‖ ≤ H * ‖a 0‖)
    (hrep : ∀ r < m, a 0 • ψ r + ∑ s ∈ (range m).filter (r < ·), a (s - r) • ψ s =
      (r.factorial : ℂ) • η r) :
    ∀ r < m, ‖a 0‖ * q (ψ r) ≤ m.factorial * A * (1 + m * H) ^ (m - 1 - r) := by
  refine finiteBlock_inverse_bound m (fun r ↦ ‖a 0‖ * q (ψ r)) (m.factorial * A) H
    (by positivity) hH fun r hr ↦ ?_
  let t := (range m).filter (r < ·)
  have he : a 0 • ψ r = (r.factorial : ℂ) • η r - ∑ s ∈ t, a (s - r) • ψ s :=
    eq_sub_of_add_eq (hrep r hr)
  calc
    ‖a 0‖ * q (ψ r) = q (a 0 • ψ r) := (map_smul_eq_mul _ _ _).symm
    _ ≤ q ((r.factorial : ℂ) • η r) + q (∑ s ∈ t, a (s - r) • ψ s) := he ▸ map_sub_le_add _ _ _
    _ ≤ m.factorial * A + ∑ s ∈ t, q (a (s - r) • ψ s) := by
      apply add_le_add _ (Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _)
      rw [map_smul_eq_mul, Complex.norm_natCast]
      exact mul_le_mul (by exact_mod_cast Nat.factorial_le hr.le) (hη _ hr) (apply_nonneg _ _) (by positivity)
    _ ≤ m.factorial * A + H * ∑ s ∈ t, ‖a 0‖ * q (ψ s) := by
      rw [Finset.mul_sum]
      apply add_le_add_right
      apply sum_le_sum
      intro s hs
      obtain ⟨hsm, hrs⟩ := mem_filter.mp hs
      have hsm' := Finset.mem_range.mp hsm
      rw [map_smul_eq_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (ha _ (by omega) (by omega)) (apply_nonneg _ _)

/-- A finite triangular Taylor convolution is injective when its constant term is nonzero. -/
private theorem finiteBlock_convolution_injective (a g h : ℕ → ℂ) (m : ℕ) (ha : a 0 ≠ 0)
    (he : ∀ r < m, ∑ k ∈ range (r + 1), a k * g (r - k) =
      ∑ k ∈ range (r + 1), a k * h (r - k)) : ∀ r < m, g r = h r := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr
    have hr0 : 0 ∈ range (r + 1) := by simp
    have ht : ∑ k ∈ (range (r + 1)).erase 0, a k * g (r - k) =
        ∑ k ∈ (range (r + 1)).erase 0, a k * h (r - k) := by
      refine sum_congr rfl fun k hk ↦ congrArg (a k * ·) (ih _ ?_ ?_)
      · obtain ⟨hk0, hkr⟩ := mem_erase.mp hk
        have := Finset.mem_range.mp hkr
        omega
      · omega
    have he' := he r hr
    rw [← sum_erase_add _ _ hr0, ← sum_erase_add _ _ hr0, ht, add_right_inj, Nat.sub_zero] at he'
    exact mul_left_cancel₀ ha he'

/-- Convolution of a Taylor row with a single coordinate vector. -/
private theorem finiteBlock_delta (a : ℕ → ℂ) (r j : ℕ) (z : ℂ) :
    ∑ k ∈ range (r + 1), a k * (if r - k=j then z else 0) =
      if j ≤ r then a (r - j) * z else 0 := by
  split_ifs with hj
  · rw [sum_eq_single (r - j)]
    · simp [Nat.sub_sub_self hj]
    · intro k hk hneq
      have hkr := Finset.mem_range.mp hk
      rw [ite_eq_right (show r - k ≠ j by omega), mul_zero]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  · refine sum_eq_zero fun k _ ↦ ?_
    rw [ite_eq_right (show r - k ≠ j by omega), mul_zero]

/-- Form the Fourier-biorthogonal family by transposing the finite Laurent rows.
The resulting identities give the backward recurrence for the polar vectors. -/
private theorem finiteBlock_fourier_family {C E : Type*} [AddCommGroup E] [Module ℂ E]
    [DecidableEq C] (m : C → ℕ) (a : C → ℕ → ℂ)
    (P D : C → ℕ → E →ₗ[ℂ] ℂ) (ψ : C → ℕ → E)
    (ha : ∀ c, 0 < m c → a c 0 ≠ 0)
    (hψ : ∀ c r, r < m c → ∀ b j, j < m b →
      P c r (ψ b j) = if c = b ∧ r = j then 1 else 0)
    (hrow : ∀ c r, r < m c → ∀ x,
      P c r x = ∑ k ∈ range (r + 1), a c k * (D c (r - k) x / ((r - k).factorial : ℂ))) :
    ∃ η : C → ℕ → E,
      (∀ c r, r < m c → ∀ b j, j < m b →
        D c r (η b j) = if c = b ∧ r = j then 1 else 0) ∧
      ∀ b j, j < m b → a b 0 • ψ b j +
        ∑ s ∈ (range (m b)).filter (j < ·), a b (s - j) • ψ b s =
        (j.factorial : ℂ) • η b j := by
  classical
  let η (b : C) (j : ℕ) :=
    ((j.factorial : ℂ)⁻¹) • ∑ s ∈ range (m b), (if j ≤ s then a b (s - j) else 0) • ψ b s
  refine ⟨η, ?_, ?_⟩
  · intro c r hr b j hj
    let g (s : ℕ) := D c s (η b j) / (s.factorial : ℂ)
    let h (s : ℕ) := if c = b ∧ s = j then (j.factorial : ℂ)⁻¹ else 0
    have hx (s : ℕ) (hs : s < m c) : P c s (η b j) =
        if c = b ∧ j ≤ s then a c (s - j) * (j.factorial : ℂ)⁻¹ else 0 := by
      simp only [η, map_smul, map_sum, smul_eq_mul]
      by_cases hcb : c = b
      · subst b
        rw [sum_eq_single s]
        · rw [hψ c s hs c s hs]
          simp only [and_self, ↓reduceIte, true_and, mul_one]
          split_ifs <;> ring
        · intro k hk hks
          simp [hψ c s hs c k (Finset.mem_range.mp hk), Ne.symm hks]
        · exact fun he ↦ (he (Finset.mem_range.mpr hs)).elim
      · rw [sum_eq_zero (fun k hk ↦ ?_)]
        · simp [hcb]
        · simp [hψ c s hs b k (Finset.mem_range.mp hk), hcb]
    have he := finiteBlock_convolution_injective (a c) g h (m c) (ha c (by omega)) (by
      intro s hs
      change ∑ k ∈ range (s+1), a c k * (D c (s - k) (η b j) / ((s - k).factorial : ℂ)) = _
      rw [← hrow c s hs, hx s hs]
      by_cases hcb : c = b
      · simpa only [h, hcb, true_and] using
          (finiteBlock_delta (a c) s j (j.factorial : ℂ)⁻¹).symm
      · simp [h, hcb]) r hr
    change D c r (η b j) / (r.factorial : ℂ) = _ at he
    rw [div_eq_iff (by exact_mod_cast r.factorial_ne_zero)] at he
    rw [he]
    by_cases hcr : c = b ∧ r = j
    · obtain ⟨hc, rfl⟩ := hcr
      simp [h, hc, Nat.factorial_ne_zero]
    · simp [h, hcr]
  · intro b j hj
    dsimp only [η]
    rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast j.factorial_ne_zero), one_smul]
    rw [← sum_erase_add _ _ (Finset.mem_range.mpr hj)]
    rw [ite_eq_left (le_refl _), Nat.sub_self, add_comm]
    congr 1
    simp only [ite_smul, zero_smul, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ ↦ rfl)
    ext s
    simp only [mem_filter, mem_erase, Finset.mem_range]
    omega

/-- The forward row needs only the common Laurent scale and the largest Fourier sample. -/
private theorem finiteBlock_row_bound (a g : ℕ → ℂ) (r m : ℕ) (hr : r < m) (H B : ℝ)
    (hH : 0 ≤ H) (hB : 0 ≤ B)
    (ha : ∀ k < m, ‖a k‖ ≤ H * ‖a 0‖) (hg : ∀ k < m, ‖g k‖ ≤ B) :
    ‖∑ k ∈ Finset.range (r + 1), a k * (g (r - k) / ((r - k).factorial : ℂ))‖ ≤
      m * H * ‖a 0‖ * B := by
  calc
    _ ≤ ∑ k ∈ Finset.range (r + 1), ‖a k * (g (r - k) / ((r - k).factorial : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (r + 1), (H * ‖a 0‖) * B := by
      refine Finset.sum_le_sum fun k hk ↦ ?_
      rw [norm_mul, norm_div, Complex.norm_natCast]
      have klt := Finset.mem_range.mp hk
      have hden : (1 : ℝ) ≤ (r - k).factorial := by exact_mod_cast Nat.factorial_pos _
      exact mul_le_mul (ha k (by omega))
        ((div_le_self (norm_nonneg _) hden).trans (hg _ (by omega)))
        (by positivity) (by positivity)
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [mul_assoc (m : ℝ) H, mul_assoc (m : ℝ)]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (by positivity)

/-- Combine the polynomial matrix estimates with a sufficiently high inverse-power
bound on each Fourier sample. All exponents are uniform in the row of the block. -/
private theorem finiteBlock_weight_bound (m M r d e : ℕ) (hm : m ≤ M)
    (L A H B : ℝ) (hL : 1 ≤ L) (hA : 0 ≤ A) (hH : 0 ≤ H) (hB : 0 ≤ B) :
    ((m : ℝ) * (H * L ^ d) * (B / L ^ (d + e + d * M + 2))) *
        ((m.factorial : ℝ) * (A * L ^ e) * (1 + m * (H * L ^ d)) ^ (m - 1 - r)) ≤
      (M * H * B * M.factorial * A * (1 + M * H) ^ M) / L ^ 2 := by
  have hLpos := zero_lt_one.trans_le hL
  have hrat : (m : ℝ) ≤ M := by exact_mod_cast hm
  have hfac : (m.factorial : ℝ) ≤ M.factorial := by exact_mod_cast Nat.factorial_le hm
  have hp : 1 ≤ L ^ d := one_le_pow₀ hL
  have hpow : (1 + m * (H * L ^ d)) ^ (m - 1 - r) ≤ (1 + M * H) ^ M * L ^ (d * M) := by
    rw [pow_mul, ← mul_pow]
    refine (pow_le_pow_left₀ (by positivity) ?_ _).trans (pow_le_pow_right₀ ?_ (by omega))
    · calc
        _ ≤ 1 + (M : ℝ) * (H * L ^ d) := by gcongr
        _ ≤ _ := by nlinarith
    · exact one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (by positivity)) hp
  calc
    _ ≤ ((M : ℝ) * (H * L ^ d) * (B / L ^ (d + e + d * M + 2))) *
        ((M.factorial : ℝ) * (A * L ^ e) * ((1 + M * H)^M * L^(d * M))) := by gcongr
    _ = _ := by
      rw [pow_add, pow_add, pow_add]
      field_simp

end

open Classical in
/-- The transpose of the actual centered Laurent rows produces the Fourier-biorthogonal
vectors. Back substitution bounds the scaled polar vectors in every quotient seminorm. -/
private theorem orbitalPolar_family (p : Vℚ) (ω : PontryaginDual J₁)
    (ψ : Idx(p, ω) → Q(p, ω))
    (hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalPrincipalPart i x = if i = j then 1 else 0) :
    ∃ η : Idx(p, ω) → Q(p, ω),
      (∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = η j →
        sLocalOrbitalFourierJet i x = if i = j then 1 else 0) ∧
      ∀ (j : Idx(p, ω)) (q : Seminorm ℂ Q(p, ω)) (A H : ℝ), 0 ≤ A → 0 ≤ H →
        (∀ i : Idx(p, ω), i.val.1 = j.val.1 → q (η i) ≤ A) →
        (∀ i : Idx(p, ω), i.val.1 = j.val.1 → i.val.2 ≠ 0 →
          ‖rhoCoeff(j.val.1, i.val.2)‖ ≤ H * ‖rhoCoeff(j.val.1, 0)‖) →
        let m := sLocalPrimaryPoleMultiplicity p j.val.1
        ‖rhoCoeff(j.val.1, 0)‖ * q (ψ j) ≤ m.factorial * A * (1 + m * H) ^ (m - 1 - j.val.2) := by
  classical
  let C := {c : QuasiCharacter (SIdeleQuotient F S) // ∃ i : Idx(p, ω), i.val.1 = c}
  let m (c : C) := sLocalPrimaryPoleMultiplicity (F := F) (S := S) p c.val
  let center (i : Idx(p, ω)) : C := ⟨i.val.1, i, rfl⟩
  let jof (c : C) (s : ℕ) (hs : s < m c) : Idx(p, ω) :=
    ⟨(c.val, s), c.property.choose_spec ▸ c.property.choose.property.1, hs⟩
  let a (c : C) (s : ℕ) := rhoCoeff(c.val, s)
  have hpolarKer (i : Idx(p, ω)) : Rₚ(p, ω) ≤ (sLocalOrbitalPrincipalPart i).ker := by
    intro z hz
    obtain ⟨y, hy⟩ := (Rₚ(p, ω)).mkQ_surjective (ψ i)
    have hz' : π(p, ω) z = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hz
    have he := hψ i i (y + z) (by rw [map_add, hz', add_zero, hy])
    rw [map_add, hψ i i y hy, ite_eq_left rfl] at he
    exact add_left_cancel (he.trans (add_zero (1 : ℂ)).symm)
  have hfourKer (i : Idx(p, ω)) : Rₚ(p, ω) ≤ (sLocalOrbitalFourierJet i).ker := by
    intro z hz
    obtain ⟨f, hf⟩ := (Kₛ(ω)).mkQ_surjective z
    let b := center i
    let g (k : ℕ) := iteratedDeriv k (fourierZeta(i.val.1) f) 0 / (k.factorial : ℂ)
    have hzero (r : ℕ) (hr : r < m b) : ∑ k ∈ Finset.range (r + 1), a b k * g (r - k) = 0 := by
      have he := orbitalPolar_row (jof b r hr) f
      rw [hf] at he
      exact he.symm.trans (hpolarKer (jof b r hr) hz)
    have hi : i.val.2 < m b := i.property.2
    have h := finiteBlock_convolution_injective (a b) g (fun _ ↦ 0) (m b)
      (orbitalPolar_leading i 0).1 (fun r hr ↦ by simpa only [mul_zero, Finset.sum_const_zero] using hzero r hr)
      i.val.2 hi
    have hf0 : iteratedDeriv i.val.2 (fourierZeta(i.val.1) f) 0 = 0 :=
      (div_eq_zero_iff.mp h).resolve_right (by exact_mod_cast i.val.2.factorial_ne_zero)
    change sLocalOrbitalFourierJet i z = 0
    rw [← hf]
    exact hf0
  let pol (i : Idx(p, ω)) : Q(p, ω) →ₗ[ℂ] ℂ :=
    ((Rₚ(p, ω)).liftQL (sLocalOrbitalPrincipalPart i)
      (hpolarKer i)).toLinearMap
  let four (i : Idx(p, ω)) : Q(p, ω) →ₗ[ℂ] ℂ :=
    ((Rₚ(p, ω)).liftQL (sLocalOrbitalFourierJet i)
      (hfourKer i)).toLinearMap
  let P (c : C) (s : ℕ) := if hs : s < m c then pol (jof c s hs) else 0
  let D (c : C) (s : ℕ) := if hs : s < m c then four (jof c s hs) else 0
  let ψ₀ (c : C) (s : ℕ) := if hs : s < m c then ψ (jof c s hs) else 0
  have hij (b c : C) (r s : ℕ) (hr : r < m b) (hs : s < m c) :
      jof b r hr = jof c s hs ↔ b = c ∧ r = s := by
    change (⟨_,_⟩ : Idx(p, ω)) = ⟨_,_⟩ ↔ _
    simp only [Subtype.ext_iff, Prod.mk.injEq]
    exact and_congr_left' Subtype.val_inj
  have ha (c : C) (hc : 0 < m c) : a c 0 ≠ 0 :=
    (orbitalPolar_leading (jof c 0 hc) 0).1
  have hp (c : C) (r : ℕ) (hr : r < m c) (b : C) (s : ℕ) (hs : s < m b) :
      P c r (ψ₀ b s) = if c = b ∧ r = s then 1 else 0 := by
    simp only [P, ψ₀,dite_eq_left hr, dite_eq_left hs]
    obtain ⟨y, hy⟩ := (Rₚ(p, ω)).mkQ_surjective (ψ (jof b s hs))
    rw [← hy]
    change sLocalOrbitalPrincipalPart (jof c r hr) y = _
    rw [hψ _ _ y hy, hij c b r s hr hs]
    split_ifs <;> rfl
  have hrow (c : C) (r : ℕ) (hr : r < m c) (x : Q(p, ω)) :
      P c r x = ∑ k ∈ Finset.range (r + 1), a c k * (D c (r - k) x / ((r - k).factorial : ℂ)) := by
    obtain ⟨y, rfl⟩ := (Rₚ(p, ω)).mkQ_surjective x
    obtain ⟨f, rfl⟩ := (Kₛ(ω)).mkQ_surjective y
    rw [show P c r = pol (jof c r hr) by simp [P, hr]]
    refine (orbitalPolar_row (jof c r hr) f).trans (Finset.sum_congr rfl fun k _ ↦ ?_)
    dsimp only [jof, a, D]
    rw [dite_eq_left (show r - k < m c by omega)]
    rfl
  obtain ⟨E, hE, hcol⟩ := finiteBlock_fourier_family m a P D ψ₀ ha hp hrow
  refine ⟨fun i ↦ E (center i) i.val.2, ?_, ?_⟩
  · intro i j x hx
    have hi : i.val.2 < m (center i) := i.property.2
    have hj : j.val.2 < m (center j) := j.property.2
    have he := hE (center i) _ hi (center j) _ hj
    change π(p, ω) x = E (center j) j.val.2 at hx
    rw [← hx] at he
    simp only [D, dite_eq_left hi] at he
    change sLocalOrbitalFourierJet i x = _ at he
    by_cases h : i = j
    · subst j
      simpa using he
    · have hne : ¬ (center i = center j ∧ i.val.2 = j.val.2) :=
        fun hh ↦ h ((hij _ _ _ _ hi hj).2 hh)
      simpa only [ite_eq_right hne, ite_eq_right h] using he
  · intro j q A H hA hH hE' ha'
    let c := center j
    have hj : j.val.2 < m c := j.property.2
    have hE'' (r : ℕ) (hr : r < m c) : q (E c r) ≤ A := hE' (jof c r hr) rfl
    have ha'' (r : ℕ) (hr : r < m c) (hr' : r ≠ 0) : ‖a c r‖ ≤ H * ‖a c 0‖ :=
      ha' (jof c r hr) rfl hr'
    have h := finiteBlock_biorthogonal_bound q (m c) (a c) (ψ₀ c) (E c) A H hA hH
      hE'' ha'' (hcol c) j.val.2 hj
    rw [show ψ₀ c j.val.2 = ψ j by
      rw [show ψ₀ c j.val.2 = ψ (jof c j.val.2 hj) by simp [ψ₀, hj]]
      exact congrArg ψ (Subtype.ext rfl)] at h
    exact h

/-- A lattice point determines the restriction of its unitary chart to the norm-one group. -/
private theorem orbitalPolar_chart_restriction {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (m : G →* ℝ≥0ˣ) (hm : Continuous m)
    (χ : PontryaginDual G) (z : ℂ) (ω : PontryaginDual m.ker)
    (he : normOneRestriction m (quasiCharacterNormTwist m hm ((circleToComplex).comp χ) z) =
      (circleToComplex).comp ω) :
    ω = χ.comp (⟨m.ker.subtype, continuous_subtype_val⟩ : m.ker →ₜ* G) := by
  ext x
  have h := congrArg (fun a : QuasiCharacter m.ker ↦ a x) he
  exact h.symm.trans (normOneRestriction_unitaryChart m hm χ z x)

open Classical in
/-- The Laurent row and its transposed biorthogonal column share their leading scale.
Polynomial bounds for the normalized row and column therefore combine with rapid
decay of the Fourier samples to give inverse-square decay of each polar basis term. -/
private theorem sLocalPolarOrbital_bases_of_laurent_bounds_local
    (p : Vℚ) (ω : PontryaginDual J₁)
    (hS : IsSaturatedPlaceSet S) (hp : (Sₚ(p)).Nonempty) (hPic : PicTrivial)
    (hcoeff : ∀ χ : PontryaginDual Jₛ, ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        ‖rhoCoeff(j.val.1, j.val.2)‖ ≤ C * (1 + ‖s‖) ^ d * ‖rhoCoeff(j.val.1, 0)‖)
    (ψ : Idx(p, ω) → Q(p, ω))
    (hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalPrincipalPart i x = if i = j then 1 else 0)
    (f : ℬₛ) (q : Seminorm ℂ Q(p, ω)) (hq : Continuous q) :
    ∀ (χ : PontryaginDual Jₛ) (v : S) (u : (v.val.adicCompletion F)ˣ) (t : ℝ),
      uniformizerNorm(v, u) → phase(χ, v, u, t) → ∃ C : ℝ, 0 ≤ C ∧
        ∀ (j : Idx(p, ω)) (n : ℤ), j.val.1 = lattice(χ, v, t, n) →
          v ∈ sLocalFinitePolePlaces (F := F) (S := S) j.val.1 → v.val ∈ Sₚ(p) →
            ‖sLocalOrbitalPrincipalPart j ((Kₛ(ω)).mkQ f)‖ * q (ψ j) ≤ C / (1 + |(n : ℝ)|) ^ 2 := by
  classical
  obtain ⟨η, hη, hscaled⟩ := orbitalPolar_family p ω ψ hψ
  intro χ v u t hu ht
  let s (n : ℤ) : ℂ := (((n : ℝ) * period(v) - t : ℝ) : ℂ) * Complex.I
  let L (n : ℤ) : ℝ := 1 + |(n : ℝ)|
  have hL (n : ℤ) : 1 ≤ L n := le_add_of_nonneg_right (abs_nonneg _)
  by_cases hv : v.val ∈ Sₚ(p)
  case neg => exact ⟨0, le_rfl, fun j n hc hplace hprimary ↦ (hv hprimary).elim⟩
  by_cases hω : ω = restrict₁(χ)
  case neg =>
    refine ⟨0, le_rfl, fun j n hc _ _ ↦ (hω ?_).elim⟩
    have he := @orbitalPolar_chart_restriction (SIdeleQuotient F S) _ _ _ (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous χ (s n) ω
    rw [show chart(χ) (s n) = j.val.1 from hc.symm] at he
    exact he j.property.1
  obtain ⟨e, A, hA, hboundη⟩ := sLocalFourierOrbital_biorthogonal_growth p χ ω v u t
    hS hp hPic hω hv hu ht η hη q hq
  obtain ⟨d, C, hC, hratio⟩ := hcoeff χ
  let M := Fintype.card S
  let K := 1 + |t| + |period(v)|
  let H := 1 + C * K ^ d
  have hK : 0 < K := by dsimp [K]; positivity
  have hH : 1 ≤ H := le_add_of_nonneg_right (mul_nonneg hC.le (pow_pos hK _).le)
  have hs (n : ℤ) : 1 + ‖s n‖ ≤ K * L n := by
    simp only [s, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    have htri := abs_sub ((n : ℝ) * period(v)) t
    rw [abs_mul] at htri
    dsimp [K, L]
    nlinarith [mul_nonneg (abs_nonneg t) (abs_nonneg (n : ℝ)), abs_nonneg (period(v)), abs_nonneg (n : ℝ)]
  let N := d + e + d * M + 2
  choose B hB hdec using fun k ↦ sLocalOrbitalFourierJet_lattice_schwartz_valueDecay p χ v u t hS hp hPic hv hu ht f k N
  let B' := 1 + ∑ k ∈ Finset.range M, B k
  have hB' : 0 ≤ B' := add_nonneg zero_le_one (Finset.sum_nonneg fun k _ ↦ (hB k).le)
  refine ⟨(M * H * B' * M.factorial * A * (1 + M * H) ^ M), by positivity, ?_⟩
  intro j n hc hplace _
  let m := sLocalPrimaryPoleMultiplicity p j.val.1
  have hr : j.val.2 < m := j.property.2
  have hm : m ≤ M := Finset.card_le_univ _
  let iof (k : ℕ) (hk : k < m) : Idx(p, ω) := ⟨(j.val.1, k), j.property.1, hk⟩
  have hcenter : j.val.1 = chart(χ) (s n) := hc
  have hrho (k : ℕ) (hk : k < m) :
      ‖rhoCoeff(j.val.1, k)‖ ≤ (H * L n ^ d) * ‖rhoCoeff(j.val.1, 0)‖ := by
    by_cases hk0 : k = 0
    · rw [hk0]
      exact le_mul_of_one_le_left (norm_nonneg _) (one_le_mul_of_one_le_of_one_le hH (one_le_pow₀ (hL _)))
    refine (hratio (iof k hk) (s n) hk0 hcenter).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    calc
      C * (1 + ‖s n‖)^d ≤ C * (K * L n)^d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (hs n) _) hC.le
      _ ≤ H * L n ^ d := by
        rw [mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)
  have hjet (k : ℕ) (hk : k < m) :
      ‖iteratedDeriv k (fourierZeta(j.val.1) f) 0‖ ≤ B' / L n ^ N := by
    have he := hdec k n
    rw [← hc, ite_eq_left ⟨hplace, hk⟩] at he
    have hBk : B k ≤ B' := by
      refine (Finset.single_le_sum (f := B) (fun i _ ↦ (hB i).le) (Finset.mem_range.mpr (hk.trans_le hm))).trans ?_
      exact le_add_of_nonneg_left zero_le_one
    exact he.trans (div_le_div_of_nonneg_right hBk (by positivity))
  have hpolar := finiteBlock_row_bound (fun k ↦ rhoCoeff(j.val.1, k))
    (fun k ↦ iteratedDeriv k (fourierZeta(j.val.1) f) 0) j.val.2 m hr
    (H * L n ^ d) (B' / L n ^ N) (by positivity) (by positivity) hrho hjet
  rw [← orbitalPolar_row j f] at hpolar
  have hscaled' := hscaled j q (A * L n ^ e) (H * L n ^ d) (by positivity) (by positivity)
    (fun i hi ↦ hboundη n i (hi.trans hc) (hi ▸ hplace))
    (fun i hi _ ↦ hrho i.val.2 (by simpa only [m, ← hi, sLocalPrimaryPoleMultiplicity] using i.property.2))
  calc
    _ ≤ (m * (H * L n ^ d) * (B' / L n ^ N)) * (‖rhoCoeff(j.val.1, 0)‖ * q (ψ j)) := by
      refine (mul_le_mul_of_nonneg_right hpolar (apply_nonneg _ _)).trans_eq ?_
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hscaled' (by positivity)).trans
      (finiteBlock_weight_bound m M j.val.2 d e hm (L n) A H B' (hL _) hA.le (zero_le_one.trans hH) hB')

open Classical in
/-- Paper: Theorem 7.3.1.6(3), p. 345, with its proof on pp. 346–349.
For every quotient vector, its polar coordinate terms are summable under each continuous
seminorm. This isolates the analytic estimate: combine rapid decay of the Laurent
coefficients on the finitely many local pole lattices with polynomial growth of their
biorthogonal vectors, accounting for multiplicities and overlapping lattices. -/
private theorem sLocalPolarOrbital_bases_of_laurent_bounds_primal_summable
    (p : Vℚ) (ω : PontryaginDual J₁)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial)
    (_hcoeff : ∀ χ : PontryaginDual Jₛ, ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        ‖rhoCoeff(j.val.1, j.val.2)‖ ≤ C * (1 + ‖s‖) ^ d * ‖rhoCoeff(j.val.1, 0)‖)
    (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω)))
    (_hD : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (ψ : Idx(p, ω) → Q(p, ω))
    (_hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x =
        if i = j then 1 else 0)
    (q : Seminorm ℂ Q(p, ω)) (_hq : Continuous q) (x : Q(p, ω)) :
    Summable (fun j : Idx(p, ω) ↦ q (D j x • ψ j)) := by
  classical
  obtain ⟨y, rfl⟩ := (Rₚ(p, ω)).mkQ_surjective x
  obtain ⟨f, rfl⟩ := (Kₛ(ω)).mkQ_surjective y
  have hs := sLocalPolarOrbital_bases_of_laurent_bounds_lattices p ω _
    (fun j ↦ mul_nonneg (norm_nonneg _) (apply_nonneg q (ψ j)))
    (sLocalPolarOrbital_bases_of_laurent_bounds_local p ω _hS _hp _hPic _hcoeff ψ _hψ f q _hq)
  simpa only [map_smul_eq_mul, _hD] using hs

open Classical in
/-- Paper: Theorem 7.3.1.6(3), p. 345.
With a biorthogonal family in the primary quotient, the enumeration of that family is an
absolute Schauder basis of the quotient. This is the absolute-basis clause of Theorem
7.3.1.6(3) for the polar system; it is the half of that theorem which rests on the
identification (7.3.1.19) with the modulated quotient of Theorem 4.6.1.5.
Deviation: Keeps the Laurent-ratio bound of Theorem 7.3.1.6 as stated on p. 345. -/
theorem sLocalPolarOrbital_bases_of_laurent_bounds_primal
    (p : Vℚ) (ω : PontryaginDual J₁) (σ : ℕ ≃ Idx(p, ω))
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial)
    (_hcoeff : ∀ χ : PontryaginDual Jₛ, ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        ‖rhoCoeff(j.val.1, j.val.2)‖ ≤ C * (1 + ‖s‖) ^ d * ‖rhoCoeff(j.val.1, 0)‖)
    (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω)))
    (_hD : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (ψ : Idx(p, ω) → Q(p, ω))
    (_hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x =
        if i = j then 1 else 0) :
    let e := ψ ∘ σ
    let d := D ∘ σ
    IsSchauderBasis e d ∧ SchauderBasis.IsAbsolute e d := by
  have hR : IsClosed (Rₚ(p, ω) : Set (Θₛ(ω))) :=
    (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding
      (F := F) (S := S) hₚ(p) ω).isClosed_range
  have hF : IsFrechetTVS (Q(p, ω)) :=
    isFrechetTVS_quotient (sLocalHomogeneousThetaSpace_frechet ω) _ hR
  apply sLocalPolarOrbital_bases_of_laurent_bounds_primal_of_summable p ω (ψ ∘ σ) (D ∘ σ) hF
  · intro m n
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (Rₚ(p, ω)) (ψ (σ n))
    have he := (_hD (σ m) x).trans (_hψ (σ m) (σ n) x hx)
    rw [hx] at he
    simpa only [Function.comp_apply, σ.injective.eq_iff] using he
  · intro x hx
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (Rₚ(p, ω)) x
    apply (sLocalPrimaryOrbitalQuotient_mk_eq_zero p _hS _hp _hPic ω y).mpr
    intro j
    obtain ⟨n, rfl⟩ := σ.surjective j
    exact (_hD (σ n) y).symm.trans (hx n)
  · intro q hq x
    exact σ.summable_iff.mpr
      (sLocalPolarOrbital_bases_of_laurent_bounds_primal_summable
        p ω _hS _hp _hPic _hcoeff D _hD ψ _hψ q hq x)

open Classical in
/-- Paper: Theorem 7.3.1.6(2), p. 345.
With a biorthogonal family in the primary quotient, the enumeration of the polar
functionals is an unconditional Schauder basis of the strong dual. This is the
strong-dual clause of Theorem 7.3.1.6(2) for the polar system.
Deviation: Keeps the Laurent-ratio bound of Theorem 7.3.1.6 as stated on p. 345. -/
theorem sLocalPolarOrbital_bases_of_laurent_bounds_dual
    (p : Vℚ) (ω : PontryaginDual J₁) (σ : ℕ ≃ Idx(p, ω))
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial)
    (_hcoeff : ∀ χ : PontryaginDual Jₛ, ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        ‖rhoCoeff(j.val.1, j.val.2)‖ ≤ C * (1 + ‖s‖) ^ d * ‖rhoCoeff(j.val.1, 0)‖)
    (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω)))
    (_hD : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (ψ : Idx(p, ω) → Q(p, ω))
    (_hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x =
        if i = j then 1 else 0) :
    let d := D ∘ σ
    let ev : ℕ → StrongDual ℂ (StrongDual ℂ (Q(p, ω))) :=
      fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (ψ (σ n))
    IsSchauderBasis d ev ∧ SchauderBasis.IsUnconditional d ev := by
  have hprimal := sLocalPolarOrbital_bases_of_laurent_bounds_primal
    p ω σ _hS _hp _hPic _hcoeff D _hD ψ _hψ
  have hR : IsClosed (Rₚ(p, ω) : Set (Θₛ(ω))) :=
    (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding
      (F := F) (S := S) hₚ(p) ω).isClosed_range
  have hF : IsFrechetTVS (Q(p, ω)) :=
    isFrechetTVS_quotient (sLocalHomogeneousThetaSpace_frechet ω) _ hR
  have hFcopy := hF
  obtain ⟨_, hpoly, hmet, hcomp⟩ := hFcopy
  have hN : IsNuclearTVS.{0} (Q(p, ω)) :=
    isNuclearTVS_quotient (sLocalHomogeneousThetaSpace_nuclear ω) _
  let : UniformSpace (Q(p, ω)) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (Q(p, ω)) := isUniformAddGroup_of_addCommGroup
  let : MontelSpace ℂ (Q(p, ω)) :=
    montelSpace_of_schwartz_frechet hF (isSchwartzTVS_of_isNuclearTVS hN)
  let : BarrelledSpace ℂ (Q(p, ω)) := isFrechetTVS_barrelled hF
  have hrefl : IsHomeomorph (ContinuousLinearMap.applyₗ
      (E := Q(p, ω)) ℂ (RingHom.id ℂ)) :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨isEmbedding_strongBidual_eval, surjective_strongBidual_eval⟩
  exact ⟨SchauderBasis.isShrinking_of_isAbsolute hcomp hrefl hprimal.1 hprimal.2,
    SchauderBasis.strongDual_isUnconditional_of_isAbsolute
      hcomp hrefl hprimal.1 hprimal.2⟩

/-- Paper: Theorem 7.3.1.6(2)–(3), p. 345.
Any enumeration of the polar functionals gives an unconditional basis of the strong dual.
With the same enumeration, its biorthogonal vectors are an absolute basis of the quotient.
Deviation: Assumes polynomial bounds on the ratios of lower to leading Laurent coefficients
of the correcting factor within each selected block. The hypothesis is vacuous at a
primary pole of multiplicity one. The general assertion on p. 349 needs uniform control
of the changes of basis across the different centers. -/
theorem sLocalPolarOrbital_bases_of_laurent_bounds
    (p : Vℚ) (ω : PontryaginDual J₁)
    (_hS : IsSaturatedPlaceSet S) (_hp : (Sₚ(p)).Nonempty) (_hPic : PicTrivial) (σ : ℕ ≃ Idx(p, ω))
    (_hcoeff : ∀ χ : PontryaginDual Jₛ, ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        ‖rhoCoeff(j.val.1, j.val.2)‖ ≤ C * (1 + ‖s‖) ^ d * ‖rhoCoeff(j.val.1, 0)‖) :
    ∃ (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω))) (ψ : Idx(p, ω) → Q(p, ω))
      (ev : ℕ → StrongDual ℂ (StrongDual ℂ (Q(p, ω)))),
      (∀ (n : ℕ) (ℓ : StrongDual ℂ (Q(p, ω))), ev n ℓ = ℓ (ψ (σ n))) ∧
      (∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x) ∧
      let e := ψ ∘ σ
      let d := D ∘ σ
      IsSchauderBasis d ev ∧ SchauderBasis.IsUnconditional d ev ∧
        IsSchauderBasis e d ∧ SchauderBasis.IsAbsolute e d := by
  classical
  obtain ⟨D, hD⟩ : ∃ D : Idx(p, ω) → StrongDual ℂ (Q(p, ω)),
      ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x :=
    sLocalPolarOrbital_bases_of_laurent_bounds_descend (F := F) (S := S) p ω
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Idx(p, ω) → Q(p, ω),
      ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x =
          if i = j then 1 else 0 :=
    sLocalPolarOrbital_bases_of_laurent_bounds_biorthogonal (F := F) (S := S) p ω _hS _hp _hPic
  have hprimal := sLocalPolarOrbital_bases_of_laurent_bounds_primal (F := F) (S := S)
    p ω σ _hS _hp _hPic _hcoeff D hD ψ hψ
  have hdual := sLocalPolarOrbital_bases_of_laurent_bounds_dual (F := F) (S := S)
    p ω σ _hS _hp _hPic _hcoeff D hD ψ hψ
  exact ⟨D, ψ, fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (ψ (σ n)),
    fun n ℓ ↦ rfl, hD, hdual.1, hdual.2, hprimal.1, hprimal.2⟩

end PolarLaurentBases

-- TODO(paper-gap): The proof of Theorem 7.3.1.6 alternates between 1+s and 1-s in
-- (7.3.1.24)–(7.3.1.25). For the displayed 1+s coordinate the multiplier is P(-s)
-- for P(s) the selected reciprocal Euler product. The remaining order at c can be
-- m_S(c) - N_p(c), which is positive when other places contribute there.
-- The pointwise triangular changes on p. 349 need a convergence argument for the polar basis.
-- The discrete oscillation assertion on p. 350 needs the estimate identified in ERRATA M8.

section OrbitalSystems

open Classical in
/-- Paper: Definition 7.3.1.7(1), p. 350.
The polar orbital system consists of the primary polar functionals in the ambient strong
dual and their biorthogonal vectors in the quotient. -/
def sLocalPolarOrbitalSystem (p : Vℚ) (ω : PontryaginDual J₁) : Set (StrongDual ℂ (Θₛ(ω))) × Set Q(p, ω) :=
  (range (sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω)),
    {y : Q(p, ω) | ∃ j : Idx(p, ω), ∀ (i : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = y →
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0})

open Classical in
/-- Paper: Definition 7.3.1.7(2), p. 350.
The fourier orbital system consists of the primary fourier functionals in the ambient strong
dual and their biorthogonal vectors in the quotient. -/
def sLocalFourierOrbitalSystem (p : Vℚ) (ω : PontryaginDual J₁) : Set (StrongDual ℂ (Θₛ(ω))) × Set Q(p, ω) :=
  (range (sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω)),
    {y : Q(p, ω) | ∃ j : Idx(p, ω), ∀ (i : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = y →
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0})

/-- Paper: Definition 7.3.1.7(1), p. 350.
Each selected Laurent coefficient belongs to the polar orbital system's functional set. -/
theorem sLocalOrbitalPrincipalPart_mem_polarSystem (p : Vℚ) (ω : PontryaginDual J₁) (j : Idx(p, ω)) :
    sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j ∈
      (sLocalPolarOrbitalSystem (F := F) (S := S) p ω).1 := ⟨j, rfl⟩

/-- Paper: Definition 7.3.1.7(2), p. 350.
Each selected Fourier jet belongs to the Fourier orbital system's functional set. -/
theorem sLocalOrbitalFourierJet_mem_fourierSystem (p : Vℚ) (ω : PontryaginDual J₁) (j : Idx(p, ω)) :
    sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j ∈
      (sLocalFourierOrbitalSystem (F := F) (S := S) p ω).1 := ⟨j, rfl⟩

open Classical in
/-- Paper: Definition 7.3.1.7(1), p. 350.
The quotient vector paired with a specified index belongs to the system's second set. -/
theorem sLocalPolarOrbitalSystem_biorthogonal_mem (p : Vℚ) (ω : PontryaginDual J₁)
    (ψ : Idx(p, ω) → Q(p, ω))
    (hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0)
    (j : Idx(p, ω)) : ψ j ∈ (sLocalPolarOrbitalSystem (F := F) (S := S) p ω).2 :=
  ⟨j, fun i ↦ hψ i j⟩

open Classical in
/-- Paper: Definition 7.3.1.7(2), p. 350.
The quotient vector paired with a specified index belongs to the system's second set. -/
theorem sLocalFourierOrbitalSystem_biorthogonal_mem (p : Vℚ) (ω : PontryaginDual J₁)
    (ψ : Idx(p, ω) → Q(p, ω))
    (hψ : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = ψ j →
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x = if i = j then 1 else 0)
    (j : Idx(p, ω)) : ψ j ∈ (sLocalFourierOrbitalSystem (F := F) (S := S) p ω).2 :=
  ⟨j, fun i ↦ hψ i j⟩

end OrbitalSystems

-- TODO(paper-gap): Corollary 7.3.1.8 cites the nonexistent Theorem 7.3.1.2(3).
-- Definition 7.3.1.7 identifies the S-local systems from Theorem 7.3.1.6.
-- The proof also mentions global systems but does not identify a global orbital quotient or basis.

section OrbitalBasisProperties

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F


/-- The primary orbital quotient is a nuclear Fréchet space, and evaluation into its strong
bidual is a homeomorphism. -/
private theorem sLocalOrbitalSystem_quotient_nuclearFrechet (p : Vℚ) (ω : PontryaginDual J₁) :
    IsFrechetTVS (Q(p, ω)) ∧ IsNuclearTVS.{0} (Q(p, ω)) ∧
      IsHomeomorph (ContinuousLinearMap.applyₗ (E := Q(p, ω)) ℂ (RingHom.id ℂ)) := by
  have hR : IsClosed (Rₚ(p, ω) : Set (Θₛ(ω))) :=
    (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding (F := F) (S := S) hₚ(p) ω).isClosed_range
  have hF : IsFrechetTVS (Q(p, ω)) :=
    isFrechetTVS_quotient (sLocalHomogeneousThetaSpace_frechet ω) _ hR
  have hT2 : T2Space (Θₛ(ω) ⧸ Rₚ(p, ω)) := by
    obtain ⟨_, _, hmet, _⟩ := hF
    let : TopologicalSpace.MetrizableSpace (Θₛ(ω) ⧸ Rₚ(p, ω)) := hmet
    infer_instance
  have hN : IsNuclearTVS.{0} (Q(p, ω)) :=
    isNuclearTVS_quotient (sLocalHomogeneousThetaSpace_nuclear ω) _
  have hmon := montelSpace_of_schwartz_frechet hF (isSchwartzTVS_of_isNuclearTVS hN)
  have hbar := isFrechetTVS_barrelled hF
  refine ⟨hF, hN, ?_⟩
  obtain ⟨_, hpoly, hmet, _⟩ := hF
  let : UniformSpace (Q(p, ω)) := IsTopologicalAddGroup.rightUniformSpace (Q(p, ω))
  have : IsUniformAddGroup (Q(p, ω)) := isUniformAddGroup_of_addCommGroup
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨isEmbedding_strongBidual_eval, surjective_strongBidual_eval⟩

/-- Paper: Corollary 7.3.1.8(1), p. 350.
The enumerated polar and Fourier systems give equicontinuous, shrinking and boundedly
complete bases of the strong dual.
Deviation: Assumes a basis in the S-local quotient. The printed reference to
Theorem 7.3.1.2(3) has no target. -/
theorem sLocalOrbitalSystem_strongDual_basis_properties
    (p : Vℚ) (χ : PontryaginDual C𝔽) (χₛ : PontryaginDual Jₛ) (ω : PontryaginDual J₁)
    (σ : ℕ ≃ Idx(p, ω)) (e : ℕ → Q(p, ω)) (d : ℕ → StrongDual ℂ (Q(p, ω)))
    (hχ : (circleToComplex).comp χ ∈ unramifiedOutside F S)
    (_hχₛ : (circleToComplex).comp χₛ = sIdeleRestriction F S ⟨(circleToComplex).comp χ, hχ⟩)
    (_hω : ω = restrict₁(χₛ))
    (_hd : (∀ (n : ℕ) (x : Θₛ(ω)), d n (π(p, ω) x) =
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x) ∨
      (∀ (n : ℕ) (x : Θₛ(ω)), d n (π(p, ω) x) =
        sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x))
    (_he : IsSchauderBasis e d) :
    let ev : ℕ → StrongDual ℂ (StrongDual ℂ (Q(p, ω))) :=
      fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (e n)
    SchauderBasis.IsEquicontinuous d ev ∧ SchauderBasis.IsShrinking d ev ∧
      SchauderBasis.IsBoundedlyComplete d := by
  intro ev
  obtain ⟨hF, hN, hrefl⟩ := sLocalOrbitalSystem_quotient_nuclearFrechet (F := F) (S := S) p ω
  have habs := SchauderBasis.isAbsolute_of_nuclear_frechet hN hF _he
  have hbar := isFrechetTVS_barrelled hF
  obtain ⟨_, hpoly, _, hcomp⟩ := hF
  have hdb : IsSchauderBasis d ev := SchauderBasis.isShrinking_of_isAbsolute hcomp hrefl _he habs
  have heq : SchauderBasis.IsEquicontinuous d ev := by
    let D := StrongDual ℂ (Q(p, ω))
    let : UniformSpace (Q(p, ω)) := IsTopologicalAddGroup.rightUniformSpace (Q(p, ω))
    have : IsUniformAddGroup (Q(p, ω)) := isUniformAddGroup_of_addCommGroup
    let : PolynormableSpace ℂ D :=
      uniformConvergenceCLM_polynormable (F := ℂ) {B : Set (Q(p, ω)) | Bornology.IsVonNBounded ℂ B}
        (fun _ h ↦ h) (by rw [Bornology.sUnion_isVonNBounded_eq_univ, Submodule.span_univ]; simp)
    have : BarrelledSpace ℂ D := barrelled_of_barrel_nbhd fun B hB hBabs hBabsorb ↦
      strongDual_barrel_nbhd (fun l ↦ (hrefl.surjective l).elim fun z hz ↦ ⟨z, fun φ ↦ hz ▸ rfl⟩)
        B hB hBabs hBabsorb
    let : UniformSpace D := IsTopologicalAddGroup.rightUniformSpace D
    have : IsUniformAddGroup D := isUniformAddGroup_of_addCommGroup
    have htend (z : D) :
        Tendsto (fun k ↦ SchauderBasis.partialProjection d ev k z) atTop (𝓝 z) := by
      have hsum := hdb.2 z
      rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff] at hsum
      simpa only [Function.comp_def, ContinuousLinearMap.coe_coe,
        SchauderBasis.partialProjection, ← Nat.range_succ_eq_Iic,
        sum_apply, ContinuousLinearMap.smulRight_apply]
        using hsum.comp (tendsto_add_atTop_nat 1)
    exact (PolynormableSpace.banach_steinhaus (𝓕 := SchauderBasis.partialProjection d ev)
      (fun z ↦ (htend z).isVonNBounded_range ℂ)).equicontinuous 0
  exact ⟨heq, SchauderBasis.strongDual_isShrinking_of_isAbsolute hcomp hrefl _he habs hN,
    SchauderBasis.strongDual_isBoundedlyComplete_of_isAbsolute hcomp hrefl _he habs⟩

/-- Paper: Corollary 7.3.1.8(2), p. 350.
The corresponding biorthogonal bases of the primary quotient are equicontinuous,
shrinking and boundedly complete.
Deviation: Assumes a basis in the S-local quotient associated to the descended character. -/
theorem sLocalOrbitalSystem_quotient_basis_properties
    (p : Vℚ) (χ : PontryaginDual C𝔽) (χₛ : PontryaginDual Jₛ) (ω : PontryaginDual J₁)
    (σ : ℕ ≃ Idx(p, ω)) (e : ℕ → Q(p, ω)) (d : ℕ → StrongDual ℂ (Q(p, ω)))
    (hχ : (circleToComplex).comp χ ∈ unramifiedOutside F S)
    (_hχₛ : (circleToComplex).comp χₛ = sIdeleRestriction F S ⟨(circleToComplex).comp χ, hχ⟩)
    (_hω : ω = restrict₁(χₛ))
    (_hd : (∀ (n : ℕ) (x : Θₛ(ω)), d n (π(p, ω) x) =
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x) ∨
      (∀ (n : ℕ) (x : Θₛ(ω)), d n (π(p, ω) x) =
        sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) (σ n) x))
    (_he : IsSchauderBasis e d) :
    SchauderBasis.IsEquicontinuous e d ∧ SchauderBasis.IsShrinking e d ∧
      SchauderBasis.IsBoundedlyComplete e := by
  obtain ⟨hF, hN, hrefl⟩ := sLocalOrbitalSystem_quotient_nuclearFrechet (F := F) (S := S) p ω
  have habs := SchauderBasis.isAbsolute_of_nuclear_frechet hN hF _he
  have hbar := isFrechetTVS_barrelled hF
  obtain ⟨_, hpoly, _, hcomp⟩ := hF
  have heq : SchauderBasis.IsEquicontinuous e d := by
    let : UniformSpace (Q(p, ω)) := IsTopologicalAddGroup.rightUniformSpace (Q(p, ω))
    have : IsUniformAddGroup (Q(p, ω)) := isUniformAddGroup_of_addCommGroup
    have htend (z : Q(p, ω)) :
        Tendsto (fun k ↦ SchauderBasis.partialProjection e d k z) atTop (𝓝 z) := by
      have hsum := _he.2 z
      rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff] at hsum
      simpa only [Function.comp_def, ContinuousLinearMap.coe_coe,
        SchauderBasis.partialProjection, ← Nat.range_succ_eq_Iic,
        sum_apply, ContinuousLinearMap.smulRight_apply]
        using hsum.comp (tendsto_add_atTop_nat 1)
    exact (PolynormableSpace.banach_steinhaus (𝓕 := SchauderBasis.partialProjection e d)
      (fun z ↦ (htend z).isVonNBounded_range ℂ)).equicontinuous 0
  exact ⟨heq, SchauderBasis.isShrinking_of_isAbsolute hcomp hrefl _he habs,
    SchauderBasis.isBoundedlyComplete_of_isAbsolute hcomp hrefl _he habs⟩

end OrbitalBasisProperties

end RiemannMasullo
