module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
public import RiemannMasullo.Ch13_ZerosHecke.Targets

/-! # The exterior zeros over ℚ under Dirichlet GRH

`traceFormula_exteriorZeros` (Theorem 12.5.1.1, pp. 519–520) is a recorded gap: for a test
vanishing on the norm-one classes, the zero terms outside an open strip of positive half-width
sum to zero. `hasSum_exteriorZeros_iff_isEmpty` reduces it, at each width, to the absence of
such zeros. This file proves, for F = ℚ, that the absence follows from Dirichlet GRH stated
exactly as the target `DirichletLNonvanishingRightOfHalf` (`Statements.lean`), taken as a
hypothesis; the project's own proof of the endpoint is not used.

* **Character classification (unconditional).** A unitary character of the idele class group
  of ℚ trivial on a norm section comes from a primitive Dirichlet character with the same
  finite L-function (`exists_primitive_finiteHeckeL_eq_of_trivial_on_section`). The proof uses
  compatibility
  of the idelic Dirichlet character with change of level, surjectivity of the residue map, the
  local conductor exponents, Euler's theorem, the decomposition `C_ℚ ≅ ℝ_{>0} × ∏ 𝒪_v^×`
  and
  density of finitely supported tuples in that product.
* **Order comparison.** Under Dirichlet GRH the completed Hecke L-function of such a character
  has no zero with `Re s > 1/2`; the left half follows from the functional equation for the
  inverse character (`introTrace_completedL_no_left_zeros`).
* **Converse.** A zero of a Dirichlet L-function with `1/2 < Re s < 1` gives, through its
  primitive character and the section `t ↦ e(t, 1)` of the decomposition, an exterior zero of
  width `Re s − 1/2`. Hence `traceFormula_exteriorZeros_rat_iff_dirichletGRH`.
* **One section, countably many widths.** A finite-order character is trivial along every norm
  section, so a single section and the half-widths `1/(n+1)` already detect every off-line zero
  (`traceFormula_exteriorZeros_rat_reciprocalWidths_iff_dirichletGRH`).
-/

@[expose] public noncomputable section

open NumberFieldKB.Chebotarev.RatIdele NumberField
open Filter Function IsDedekindDomain MeasureTheory Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

/-- Reductions of a `p`-adic number are compatible: reducing modulo `p^e` and then modulo
`p^e'` (`e' ≤ e`) is reducing modulo `p^e'`. -/
private theorem cast_redP {p : ℕ} {hp : p.Prime} {e e' : ℕ} (h : e' ≤ e) (z : Kp p hp) :
    (ZMod.cast (redP p hp e z) : ZMod (p ^ e')) = redP p hp e' z := by
  have := Fact.mk hp
  unfold redP
  split_ifs with hz
  · simp only [redO]
    exact PadicInt.cast_toZModPow e' e h _
  · simp

/-- The Chinese remainder components of `a : ZMod n` are its reductions. -/
private theorem equivPi_apply_eq_cast {n : ℕ} (hn : n ≠ 0) (a : ZMod n) (p : n.primeFactors) :
    ZMod.equivPi n hn a p = (ZMod.cast a : ZMod ((p : ℕ) ^ n.factorization p)) := by
  have hdvd : (p : ℕ) ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
  have := congr($(Subsingleton.elim
    ((Pi.evalRingHom (fun p : n.primeFactors ↦ ZMod ((p : ℕ) ^ n.factorization p)) p).comp
      (ZMod.equivPi n hn).toRingHom)
    (ZMod.castHom hdvd (ZMod ((p : ℕ) ^ n.factorization p)))) a)
  simpa using this

/-- Reducing twice is reducing once. -/
private theorem cast_cast_of_dvd {n a b : ℕ} [NeZero n] (h1 : a ∣ n) (h2 : b ∣ a)
    (y : ZMod n) :
    (ZMod.cast (ZMod.cast y : ZMod a) : ZMod b) = ZMod.cast y := by
  have := congr($(Subsingleton.elim ((ZMod.castHom h2 (ZMod b)).comp (ZMod.castHom h1 (ZMod a)))
    (ZMod.castHom (h2.trans h1) (ZMod b))) y)
  simp only [RingHom.comp_apply, ZMod.castHom_apply] at this
  exact this

/-- **The residue map is compatible with change of level.** -/
private theorem castHom_resMod {m d : ℕ} [NeZero m] [NeZero d] (hd : d ∣ m) (x : IdQ) :
    ZMod.castHom hd (ZMod d) (resMod m x) = resMod d x := by
  apply (ZMod.equivPi d (NeZero.ne d)).injective
  funext p
  have hpd : (p : ℕ) ∈ d.primeFactors := p.2
  have hpm : (p : ℕ) ∈ m.primeFactors := Nat.primeFactors_mono hd (NeZero.ne m) hpd
  have hle : d.factorization p ≤ m.factorization p :=
    (Nat.factorization_le_iff_dvd (NeZero.ne d) (NeZero.ne m)).mpr hd p
  have hpow : (p : ℕ) ^ d.factorization p ∣ (p : ℕ) ^ m.factorization p := pow_dvd_pow _ hle
  -- right side: the defining components at level `d`
  rw [resMod_apply d x, resModFun, RingEquiv.apply_symm_apply]
  -- left side: reduce through `p ^ v_p(m)`
  rw [equivPi_apply_eq_cast, ZMod.castHom_apply,
    cast_cast_of_dvd hd (Nat.ordProj_dvd d p),
    ← cast_cast_of_dvd (Nat.ordProj_dvd m p) hpow]
  have hm : (ZMod.cast (resMod m x) : ZMod ((p : ℕ) ^ m.factorization p)) =
      redP p (Nat.prime_of_mem_primeFactors hpm) (m.factorization p)
        (compV (placeP m ⟨p, hpm⟩) (unitPart x)).val := by
    refine (equivPi_apply_eq_cast (NeZero.ne m) (resMod m x) ⟨p, hpm⟩).symm.trans ?_
    rw [resMod_apply, resModFun, RingEquiv.apply_symm_apply]
  rw [hm]
  exact cast_redP hle _

/-- **The idelic character is compatible with change of level.** -/
private theorem ideleChar_changeLevel {m d : ℕ} [NeZero m] [NeZero d] (hd : d ∣ m)
    (χ : DirichletCharacter ℂ d) :
    ideleChar m (DirichletCharacter.changeLevel hd χ) = ideleChar d χ := by
  ext x
  rw [coe_ideleChar, coe_ideleChar]
  congr 1
  change DirichletCharacter.changeLevel hd χ (resMod m x) = χ (resMod d x)
  have hu : IsUnit (resMod m x) := ((resMod m).toHomUnits x).isUnit
  rw [show resMod m x = ((hu.unit : (ZMod m)ˣ) : ZMod m) from rfl,
    DirichletCharacter.changeLevel_eq_cast_of_dvd χ hd hu.unit, IsUnit.unit_spec,
    ← castHom_resMod hd x, ZMod.castHom_apply]

/-! ### Factoring through the units modulo N, and passing to the primitive character -/

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ

/-- The residue map hits every unit modulo `N`. -/
private theorem resMod_toHomUnits_surjective (N : ℕ) [NeZero N] :
    Function.Surjective (resMod N).toHomUnits := by
  intro a
  let n := (a.val : ZMod N).val
  have hn : (n : ZMod N) = a.val := ZMod.natCast_zmod_val _
  have hcop := (ZMod.isUnit_iff_coprime n N).mp (hn ▸ a.isUnit)
  have hval (q : N.primeFactors) : Valued.v (n : (placeP N q).adicCompletion ℚ) = 1 := by
    have hpN : pr (placeP N q) ∣ N := by
      rw [placeP, pr_placeOf]; exact Nat.dvd_of_mem_primeFactors q.2
    rw [← Rat.cast_natCast, valued_ratCast,
      show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) by simp,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff, natCast_mem_asIdeal_iff]
    exact (pr_prime _).coprime_iff_not_dvd.mp (hcop.symm.coprime_dvd_left hpN)
  let u (q : N.primeFactors) : ((placeP N q).adicCompletion ℚ)ˣ :=
    Units.mk0 (n : (placeP N q).adicCompletion ℚ) (fun h ↦ by have := hval q; simp [h] at this)
  let y (q : N.primeFactors) : IdQ := IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ (placeP N q) (u q)
  let x : IdQ := ∏ q, y q
  have hinj : Function.Injective (placeP N) := fun q q' h ↦ by
    apply Subtype.ext
    have := congrArg pr h
    simpa [placeP, pr_placeOf] using this
  have hrat : ratPart x = 1 := by
    simp only [x, map_prod]
    refine Finset.prod_eq_one fun q _ ↦ ?_
    rw [ratPart_ofAdicCompletion _ (u q) 0 (by simpa [u] using hval q), zpow_zero]
  have hunit : unitPart x = x := by simp [unitPart_apply, hrat]
  have hcomp (q : N.primeFactors) : compV (placeP N q) x = u q := by
    simp only [x, map_prod]
    rw [Finset.prod_eq_single q]
    · exact compV_ofAdicCompletion_self _ _
    · intro q' _ hq'
      exact compV_ofAdicCompletion_ne (fun h ↦ hq' (hinj h.symm)) _
    · intro h; exact absurd (Finset.mem_univ q) h
  refine ⟨x, Units.ext ?_⟩
  change resMod N x = a.val
  apply (ZMod.equivPi N (NeZero.ne N)).injective
  rw [resMod_apply, resModFun, RingEquiv.apply_symm_apply, ← hn, map_natCast]
  funext q
  change redP q.val _ (N.factorization q) (compV (placeP N q) (unitPart x)).val = (n : ZMod _)
  rw [hunit, hcomp]
  exact redP_natCast n

/-- If `ψ` is trivial on the kernel of the residue map modulo `N`, it is the idelic
character of a Dirichlet character modulo `N`. -/
private theorem exists_dirichlet_of_ker (ψ : PontryaginDual Cℚ) (N : ℕ) [NeZero N]
    (hker : ∀ x : IdQ, resMod N x = 1 → ψ (QuotientGroup.mk x) = 1) :
    ∃ χ : DirichletCharacter ℂ N, ∀ x : IdQ,
      (ψ (QuotientGroup.mk x) : ℂ) = ((ideleChar N χ x : ℂˣ) : ℂ) := by
  let f : IdQ →* (ZMod N)ˣ := (resMod N).toHomUnits
  let g : IdQ →* ℂˣ := (Circle.toUnits.comp
    ((ψ : Cℚ →* Circle).comp (QuotientGroup.mk' _)))⁻¹
  have hfg : f.ker ≤ g.ker := by
    intro x hx
    have h1 : resMod N x = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hx)
      simpa [f] using this
    have h2 := hker x h1
    simp [g, MonoidHom.mem_ker, h2]
  let φ := f.liftOfSurjective (resMod_toHomUnits_surjective N) ⟨g, hfg⟩
  refine ⟨MulChar.ofUnitHom φ, fun x ↦ ?_⟩
  have hφ : φ (f x) = g x := MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨g, hfg⟩ x
  rw [coe_ideleChar]
  have hU : (MulChar.ofUnitHom φ).toUnitHom = φ :=
    MulChar.equivToUnitHom.apply_symm_apply φ
  change _ = ((((MulChar.ofUnitHom φ).toUnitHom (f x) : ℂˣ) : ℂ))⁻¹
  rw [hU, hφ]
  simp [g]

/-- An idelic Dirichlet character gives a primitive Dirichlet character with the same
finite L-function. -/
private theorem exists_primitive_of_ideleChar (ψ : PontryaginDual Cℚ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (h : ∀ x : IdQ, (ψ (QuotientGroup.mk x) : ℂ) = ((ideleChar N χ x : ℂˣ) : ℂ)) :
    ∃ (M : ℕ) (_ : NeZero M) (χ' : DirichletCharacter ℂ M), χ'.IsPrimitive ∧
      ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL ψ ⟨s, hs⟩ = LSeries (χ' ·) s := by
  have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hprim := χ.primitiveCharacter_isPrimitive
  obtain ⟨ψ', -, hval, hL⟩ :=
    DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hprim
  have hψ : ψ' = ψ := by
    ext g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hval x, h x, ← ideleChar_changeLevel χ.conductor_dvd_level,
      DirichletCharacter.changeLevel_primitiveCharacter]
  exact ⟨χ.conductor, inferInstance, χ.primitiveCharacter, hprim, hψ ▸ hL⟩

/-! ### Characters trivial on a norm section are determined by finite levels -/

set_option quotPrecheck false

local notation "Uℚ" => (v : Pl) → (v.adicCompletionIntegers ℚ)ˣ
local notation "qv(" v ")" => (Ideal.absNorm (IsDedekindDomain.HeightOneSpectrum.asIdeal v) : ℝ)
local notation "coord(" h ", " v ")" => ((h v).val.val)

/-- The residue modulo `N` of a tuple of local integral units. -/
private noncomputable def residueOf (N : ℕ) [NeZero N] (h : Uℚ) : ZMod N :=
  (ZMod.equivPi N (NeZero.ne N)).symm fun p ↦
    redP p (Nat.prime_of_mem_primeFactors p.2) (N.factorization p) coord(h, placeP N p)

/-- An idele with positive real coordinate and integral unit finite coordinates `h` has
residue `residueOf N h`. -/
private theorem resMod_of_coords (N : ℕ) [NeZero N] (g : IdQ) (t : ℝ≥0ˣ) (h : Uℚ)
    (ht : eInf ((g : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace) = (t : ℝ))
    (hg : ∀ v, (g : AdeleRing (𝓞 ℚ) ℚ).2 v = coord(h, v)) :
    resMod N g = residueOf N h := by
  have hginv (v : Pl) : ((g⁻¹ : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 v = ((h v)⁻¹).val.val := by
    have hmul :
        ((g⁻¹ : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 v * (g : AdeleRing (𝓞 ℚ) ℚ).2 v = 1 := by
      exact congrArg (fun a : AdeleRing (𝓞 ℚ) ℚ ↦ a.2 v) (Units.inv_mul g)
    rw [hg] at hmul
    have hu : ((h v)⁻¹).val.val * (h v).val.val = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Subring.coe_one]
    exact mul_right_cancel₀ (by
      intro h0; rw [h0, mul_zero] at hu; exact zero_ne_one hu) (hmul.trans hu.symm)
  have hrat : ratPart g = 1 := by
    refine ratPart_eq_one_of (by
        rw [NumberFieldKB.Chebotarev.RatIdele.realPart, ht]
        exact NNReal.coe_pos.mpr (Units.zero_lt t))
      fun v ↦ ⟨?_, ?_⟩
    · rw [hg]; exact (h v).val.2
    · rw [hginv]; exact ((h v)⁻¹).val.2
  have hunit : unitPart g = g := by simp [unitPart_apply, hrat]
  rw [resMod_apply, resModFun, residueOf, hunit]
  congr 1
  funext p
  rw [coe_compV, hg]

/-- The residue map is constant on idele classes. -/
private theorem resMod_eq_of_mk_eq (N : ℕ) [NeZero N] {x y : IdQ}
    (h : (QuotientGroup.mk x : Cℚ) = QuotientGroup.mk y) : resMod N x = resMod N y := by
  obtain ⟨a, ha⟩ := QuotientGroup.eq.mp h
  have h1 : resMod N (x⁻¹ * y) = 1 := by rw [← ha]; exact resMod_diag N a
  rw [map_mul] at h1
  have hu : IsUnit (resMod N x) := ((resMod N).toHomUnits x).isUnit
  have hinv : resMod N x⁻¹ * resMod N x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc resMod N x = resMod N x * (resMod N x⁻¹ * resMod N y) := by rw [h1, mul_one]
    _ = (resMod N x⁻¹ * resMod N x) * resMod N y := by ring
    _ = resMod N y := by rw [hinv, one_mul]

/-- A unit whose reduction modulo `p^e` is one is within `p^{-e}` of one. -/
private theorem valued_sub_one_le_of_redP_eq_one {p : ℕ} {hp : p.Prime} {e : ℕ} (z : Kp p hp)
    (hz : Valued.v z ≤ 1) (h : redP p hp e z = 1) :
    Valued.v (z - 1) ≤ WithZero.exp (-(e : ℤ)) := by
  have := Fact.mk hp
  let Φ := PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) (⟨p, hp⟩ : Nat.Primes)
  rw [redP_of_le hz] at h
  have h0 : PadicInt.toZModPow e (Φ.symm ⟨z, hz⟩ - 1) = 0 := by
    rw [map_sub, map_one]
    change PadicInt.toZModPow e (Φ.symm ⟨z, hz⟩) - 1 = 0
    rw [show PadicInt.toZModPow e (Φ.symm ⟨z, hz⟩) = redO p hp e ⟨z, hz⟩ from rfl, h,
      sub_self]
  have hk : Φ.symm ⟨z, hz⟩ - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ e} := by
    rw [← PadicInt.ker_toZModPow]; exact RingHom.mem_ker.mpr h0
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hk
  let w : Op p hp := Φ b
  have h2 : Φ.symm (⟨z, hz⟩ - 1) = b * (p : ℤ_[p]) ^ e := by
    rw [map_sub, map_one]; exact hb.symm
  have hO : (⟨z, hz⟩ : Op p hp) - 1 = w * (p : Op p hp) ^ e := by
    have h1 : (⟨z, hz⟩ : Op p hp) - 1 = Φ (Φ.symm (⟨z, hz⟩ - 1)) :=
      (Φ.apply_symm_apply _).symm
    rw [h1, h2, map_mul, map_pow, map_natCast]
    rfl
  have hK : z - 1 = (w : Kp p hp) * (p : Kp p hp) ^ e := by
    have := congrArg Subtype.val hO
    simpa using this
  rw [hK, map_mul, map_pow, valued_placeOf]
  have hw : Valued.v (w : Kp p hp) ≤ 1 := w.2
  calc Valued.v (w : Kp p hp) * WithZero.exp (-1) ^ e
      ≤ 1 * WithZero.exp (-1) ^ e := by gcongr
    _ = WithZero.exp (-(e : ℤ)) := by rw [one_mul, ← WithZero.exp_nsmul]; simp

/-- A unit whose reduction modulo `p^e` is one is within `p^{-e}` of one, in norm. -/
private theorem norm_sub_one_le_of_redP_eq_one {p : ℕ} {hp : p.Prime} {e : ℕ} (z : Kp p hp)
    (hz : Valued.v z ≤ 1) (h : redP p hp e z = 1) :
    ‖z - 1‖ ≤ (p : ℝ) ^ (-(e : ℤ)) := by
  have hv := valued_sub_one_le_of_redP_eq_one z hz h
  have hq : (Ideal.absNorm (placeOf p hp).asIdeal : ℝ≥0) = p := by
    rw [absNorm_asIdeal, pr_placeOf]
  have hq1 : (1 : ℝ≥0) < (Ideal.absNorm (placeOf p hp).asIdeal : ℝ≥0) := by
    rw [hq]; exact_mod_cast hp.one_lt
  have hmono := (WithZeroMulInt.toNNReal_strictMono hq1).monotone hv
  rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp] at hmono
  have hqN : Ideal.absNorm (placeOf p hp).asIdeal = p := by rw [absNorm_asIdeal, pr_placeOf]
  rw [FinitePlace.norm_def]
  calc ((WithZeroMulInt.toNNReal _ (Valued.v (z - 1)) : ℝ≥0) : ℝ)
      ≤ (((Ideal.absNorm (placeOf p hp).asIdeal : ℝ≥0) ^ (-(e : ℤ)) : ℝ≥0) : ℝ) := by
        exact_mod_cast hmono
    _ = (p : ℝ) ^ (-(e : ℤ)) := by push_cast; rw [hqN]

/-- `residueOf N` is multiplicative. -/
private theorem residueOf_mul (N : ℕ) [NeZero N] (h h' : Uℚ) :
    residueOf N (h * h') = residueOf N h * residueOf N h' := by
  rw [residueOf, residueOf, residueOf, ← map_mul]
  congr 1
  funext p
  rw [Pi.mul_apply]
  exact redP_mul (h (placeP N p)).val.2 (h' (placeP N p)).val.2

/-- `residueOf N` sends the unit tuple to one. -/
private theorem residueOf_one (N : ℕ) [NeZero N] : residueOf N 1 = 1 := by
  rw [residueOf]
  have : (fun p : N.primeFactors ↦ redP p (Nat.prime_of_mem_primeFactors p.2) (N.factorization p)
      coord((1 : Uℚ), placeP N p)) = 1 := by
    funext p; exact redP_one
  rw [this, map_one]

/-- `residueOf N` as a monoid homomorphism. -/
private noncomputable def residueHom (N : ℕ) [NeZero N] : Uℚ →* ZMod N where
  toFun := residueOf N
  map_one' := residueOf_one N
  map_mul' := residueOf_mul N

/-- **Euler.** The `φ(N)`-th power of any tuple has residue one. -/
private theorem residueOf_pow_totient (N : ℕ) [NeZero N] (h : Uℚ) :
    residueOf N (h ^ N.totient) = 1 := by
  have hu : IsUnit (residueHom N h) := (Group.isUnit h).map (residueHom N)
  change residueHom N (h ^ N.totient) = 1
  rw [map_pow]
  have := ZMod.pow_totient hu.unit
  rw [← hu.unit_spec, ← Units.val_pow_eq_pow_val, this, Units.val_one]

/-- Residue one at level `N` bounds the coordinate at every place dividing `N`. -/
private theorem norm_coord_sub_one_le_of_residueOf_eq_one (N : ℕ) [NeZero N] (h : Uℚ)
    (hres : residueOf N h = 1) (v : Pl) (hpN : pr v ∈ N.primeFactors) :
    ‖coord(h, v) - 1‖ ≤ (pr v : ℝ) ^ (-(N.factorization (pr v) : ℤ)) := by
  let P : N.primeFactors := ⟨pr v, hpN⟩
  have hcomp := congrFun (congrArg (ZMod.equivPi N (NeZero.ne N)) hres) P
  rw [residueOf, RingEquiv.apply_symm_apply, map_one] at hcomp
  have hz : Valued.v coord(h, placeP N P) ≤ 1 := (h (placeP N P)).val.2
  have hb := norm_sub_one_le_of_redP_eq_one _ hz hcomp
  have hv : placeP N P = v := ((eq_placeOf_iff v (pr v) _).mpr rfl).symm
  change ‖((h (placeP N P)).val.val : (placeP N P).adicCompletion ℚ) - 1‖ ≤ _ at hb
  rw [hv] at hb
  exact hb

/-- An integral unit is within distance one of one. -/
private theorem norm_coord_sub_one_le_one (h : Uℚ) (v : Pl) : ‖coord(h, v) - 1‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff]
  refine (Valuation.map_sub _ _ _).trans (max_le (h v).val.2 ?_)
  rw [map_one]

/-- The decomposition `C_ℚ ≅ ℝ_{>0} × ∏ 𝒪_v^×` preserves the norm:
`‖e(t, h)‖ = t`. -/
private theorem ideleClassNorm_decomposition (e : (ℝ≥0ˣ × Uℚ) ≃ₜ* Cℚ)
    (he : ∀ t h, ∃ g : IdQ,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
        (g.val.1 Rat.infinitePlace) = t.val ∧
      (∀ v, g.val.2 v = (h v).val.val) ∧ e (t, h) = QuotientGroup.mk g)
    (t : ℝ≥0ˣ) (h : Uℚ) : ideleClassNorm ℚ (e (t, h)) = t := by
  obtain ⟨g, hg1, hg2, hge⟩ := he t h
  rw [hge]
  apply Units.ext
  apply NNReal.coe_injective
  change ((ideleNorm ℚ g : ℝ≥0) : ℝ) = (t : ℝ)
  rw [((ideleNorm_spec ℚ).1 g).2]
  have hval (v : Pl) : Valued.v (h v).val.val = 1 :=
    Valuation.Integers.one_of_isUnit' (h v).isUnit (fun x ↦ x.2)
  have hfin : (∏ᶠ v : Pl, ‖g.val.2 v‖) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ by
      rw [hg2 v]; exact Valued.toNormedField.norm_eq_one_iff.mpr (hval v)
  rw [hfin, mul_one, Fintype.prod_unique]
  have hd : (default : InfinitePlace ℚ) = Rat.infinitePlace := Subsingleton.elim _ _
  rw [hd, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  have hiso := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) (g.val.1 Rat.infinitePlace)
  rw [← hiso, hg1, Real.norm_eq_abs, abs_of_pos (NNReal.coe_pos.mpr (Units.zero_lt t))]

/-- A character trivial on a norm section is trivial on the kernel of the residue map modulo
some `N`: the product of the local conductors. -/
private theorem exists_level_of_trivial_on_section (τ : ℝ≥0ˣ →ₜ* Cℚ)
    (hτ : Function.RightInverse τ (ideleClassNorm ℚ)) (ψ : PontryaginDual Cℚ)
    (hψ : ∀ t : ℝ≥0ˣ, ψ (τ t) = 1) :
    ∃ (N : ℕ) (_ : NeZero N), ∀ x : IdQ, resMod N x = 1 → ψ (QuotientGroup.mk x) = 1 := by
  obtain ⟨e, he⟩ := ratIdeleClassGroup_decomposition
  obtain ⟨n, hfin, hleast⟩ := exists_heckeConductorExponents (F := ℚ) ψ
  have hcond : ∀ (v : Pl) (u : (v.adicCompletion ℚ)ˣ), ‖u.val‖ = 1 →
      ‖u.val - 1‖ ≤ qv(v) ^ (-(n v : ℤ)) →
      ψ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 1 := fun v ↦ (hleast v).1
  let N : ℕ := ∏ v ∈ hfin.toFinset, pr v ^ n v
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ pow_ne_zero _ (pr_prime v).ne_zero
  have : NeZero N := ⟨hN0⟩
  have hNdvd (v : Pl) : pr v ^ n v ∣ N := by
    by_cases hv : v ∈ hfin.toFinset
    · exact Finset.dvd_prod_of_mem _ hv
    · rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hv
      simp [hv]
  have hbound : ∀ h : Uℚ, residueOf N h = 1 →
      ∀ v, ‖coord(h, v) - 1‖ ≤ qv(v) ^ (-(n v : ℤ)) := by
    intro h hres v
    have hq : qv(v) = (pr v : ℝ) := by exact_mod_cast absNorm_asIdeal v
    by_cases hv0 : n v = 0
    · rw [hv0, Nat.cast_zero, neg_zero, zpow_zero]
      exact norm_coord_sub_one_le_one h v
    · have hpN : pr v ∈ N.primeFactors := Nat.mem_primeFactors.mpr
        ⟨pr_prime v, dvd_trans (dvd_pow_self _ hv0) (hNdvd v), hN0⟩
      have hb := norm_coord_sub_one_le_of_residueOf_eq_one N h hres v hpN
      have hle : n v ≤ N.factorization (pr v) :=
        ((pr_prime v).pow_dvd_iff_le_factorization hN0).mp (hNdvd v)
      rw [hq]
      refine hb.trans (zpow_le_zpow_right₀ (by exact_mod_cast (pr_prime v).one_lt.le) ?_)
      exact neg_le_neg (by exact_mod_cast hle)
  -- (L3) the decomposition preserves the norm
  have hnorm : ∀ (t : ℝ≥0ˣ) (h : Uℚ), ideleClassNorm ℚ (e (t, h)) = t :=
    ideleClassNorm_decomposition e he
  -- (L6) the finite part is trivial on the conductor congruence subgroup
  have hfinite : ∀ h : Uℚ, (∀ v, ‖coord(h, v) - 1‖ ≤ qv(v) ^ (-(n v : ℤ))) →
      ψ (e (1, h)) = 1 := by
    classical
    -- the character on the finite part, as a continuous homomorphism
    let φf : Uℚ →* Circle := (ψ : Cℚ →* Circle).comp
      ((e : (ℝ≥0ˣ × Uℚ) →* Cℚ).comp (MonoidHom.inr ℝ≥0ˣ Uℚ))
    have hφc : Continuous φf :=
      ψ.continuous.comp (e.continuous.comp (continuous_const.prodMk continuous_id))
    -- (L5) a single coordinate satisfying its local bound is in the kernel
    have hsingle : ∀ (a : Pl) (u : (a.adicCompletionIntegers ℚ)ˣ),
        ‖((u : a.adicCompletionIntegers ℚ) : a.adicCompletion ℚ) - 1‖ ≤
          qv(a) ^ (-(n a : ℤ)) →
        φf (Pi.mulSingle a u) = 1 := by
      intro a u hu
      let u' : (a.adicCompletion ℚ)ˣ :=
        Units.map (a.adicCompletionIntegers ℚ).subtype.toMonoidHom u
      obtain ⟨g, hg1, hg2, hge⟩ := he 1 (Pi.mulSingle a u)
      have hgid : IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ a u' = g := by
        apply Units.ext
        apply Prod.ext
        · funext w
          have hw : w = Rat.infinitePlace := Subsingleton.elim _ _
          subst hw
          apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal
            Rat.isReal_infinitePlace).injective
          rw [hg1]
          show (InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace)
            (1 : Rat.infinitePlace.Completion) = ((1 : ℝ≥0ˣ) : ℝ)
          simp
        · ext v
          have h1 := coe_compV v (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ a u')
          rw [hg2 v]
          by_cases hv : v = a
          · subst hv
            rw [← h1, compV_ofAdicCompletion_self, Pi.mulSingle_eq_same]
            rfl
          · rw [← h1, compV_ofAdicCompletion_ne hv, Pi.mulSingle_eq_of_ne hv]
            rfl
      have hval : Valued.v ((u : a.adicCompletionIntegers ℚ) : a.adicCompletion ℚ) = 1 :=
        Valuation.Integers.one_of_isUnit' u.isUnit (fun x ↦ x.2)
      have hc := hcond a u' (Valued.toNormedField.norm_eq_one_iff.mpr hval) hu
      change ψ (e (1, Pi.mulSingle a u)) = 1
      rw [hge, ← hgid]
      exact hc
    -- truncations
    intro h hh
    let tr (T : Finset Pl) : Uℚ := fun v ↦ if v ∈ T then h v else 1
    have htr : ∀ T, φf (tr T) = 1 := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        have : tr ∅ = 1 := by funext v; simp [tr]
        rw [this, map_one]
      | insert a T ha ih =>
        have : tr (insert a T) = tr T * Pi.mulSingle a (h a) := by
          funext v
          by_cases hv : v = a
          · subst hv; simp [tr, ha]
          · simp [tr, hv]
        rw [this, map_mul, ih, hsingle a (h a) (hh a), mul_one]
    have hlim : Filter.Tendsto tr Filter.atTop (nhds h) := by
      rw [tendsto_pi_nhds]
      intro v
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop {v}] with T hT
      have : v ∈ T := hT (Finset.mem_singleton_self v)
      simp [tr, this]
    have hconst : Filter.Tendsto (fun T ↦ φf (tr T)) Filter.atTop (nhds 1) := by
      simp only [htr]; exact tendsto_const_nhds
    exact tendsto_nhds_unique ((hφc.tendsto h).comp hlim) hconst
  -- (L7) Euler: the φ(N)-th power of any tuple lies in that subgroup
  have heuler : ∀ (h : Uℚ) (v : Pl),
      ‖coord(h ^ N.totient, v) - 1‖ ≤ qv(v) ^ (-(n v : ℤ)) :=
    fun h ↦ hbound _ (residueOf_pow_totient N h)
  -- (L8) the real part is trivial
  have hreal : ∀ t : ℝ≥0ˣ, ψ (e (t, 1)) = 1 := by
    intro t
    have hk : N.totient ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)).ne'
    let r : ℝ≥0 := (t : ℝ≥0) ^ ((N.totient : ℝ)⁻¹)
    have hr0 : r ≠ 0 := (NNReal.rpow_pos (Units.zero_lt t)).ne'
    let s : ℝ≥0ˣ := Units.mk0 r hr0
    have hs : s ^ N.totient = t := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]
      exact NNReal.rpow_inv_natCast_pow _ hk)
    set ab := e.symm (τ s) with hab
    have hea : e ab = τ s := e.apply_symm_apply _
    have ha : ab.1 = s := by
      have := hnorm ab.1 ab.2
      rw [Prod.mk.eta, hea, hτ s] at this
      exact this.symm
    have hτt : τ t = e (t, ab.2 ^ N.totient) := by
      rw [← hs, map_pow, ← hea, ← map_pow]
      congr 1
      ext
      · simp [ha]
      · simp
    have h1 := hψ t
    rw [hτt,
      show ((t, ab.2 ^ N.totient) : ℝ≥0ˣ × Uℚ) = (t, 1) * (1, ab.2 ^ N.totient) by simp,
      map_mul, map_mul, hfinite _ (heuler ab.2), mul_one] at h1
    exact h1
  refine ⟨N, inferInstance, fun x hx ↦ ?_⟩
  set th := e.symm (QuotientGroup.mk x) with hth
  obtain ⟨g, hg1, hg2, hge⟩ := he th.1 th.2
  have hmk : (QuotientGroup.mk x : Cℚ) = QuotientGroup.mk g := by
    rw [← hge, Prod.mk.eta, hth]
    exact (e.apply_symm_apply _).symm
  have hres : residueOf N th.2 = 1 := by
    rw [← resMod_of_coords N g th.1 th.2 hg1 hg2, ← resMod_eq_of_mk_eq N hmk]
    exact hx
  have hloc := hbound th.2 hres
  have hsplit : e th = e (th.1, 1) * e (1, th.2) := by
    rw [← map_mul]; simp
  calc ψ (QuotientGroup.mk x) = ψ (e th) := by rw [hth, e.apply_symm_apply]
    _ = ψ (e (th.1, 1)) * ψ (e (1, th.2)) := by rw [hsplit, map_mul]
    _ = 1 := by rw [hreal, hfinite _ hloc, one_mul]

/-- A unitary character of the rational idele class group that is trivial on a norm section
comes from a primitive Dirichlet character with the same finite L-function on `Re s > 1`. -/
theorem exists_primitive_finiteHeckeL_eq_of_trivial_on_section (τ : ℝ≥0ˣ →ₜ* Cℚ)
    (hτ : Function.RightInverse τ (ideleClassNorm ℚ)) (ψ : PontryaginDual Cℚ)
    (hψ : ∀ t : ℝ≥0ˣ, ψ (τ t) = 1) :
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N), χ.IsPrimitive ∧
      ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL ψ ⟨s, hs⟩ = LSeries (χ ·) s := by
  obtain ⟨N, _, hker⟩ := exists_level_of_trivial_on_section τ hτ ψ hψ
  obtain ⟨χ, hχ⟩ := exists_dirichlet_of_ker ψ N hker
  exact exists_primitive_of_ideleChar ψ N χ hχ

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

local notation "C₁" => (ideleClassNorm ℚ).ker
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "mℚ" =>
  (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "hmℚ" => (⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ :
  IsModulation mℚ)
local notation "M(" φ ", " c ")" =>
  modulatedFourierMellin mℚ univ hmℚ μℚ (φ : BruhatCompactSupport Cℚ).val c
local notation "twist(" χ ", " s ")" => ideleClassNormTwist (F := ℚ) χ s
local notation "ord(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := ℚ) χ) univ s
local notation "zeroTerm(" φ ", " z ")" =>
  ((ord((z).val.1.val, (z).val.2) : ℤ) : ℂ) * M(φ, twist((z).val.1.val, (z).val.2 - 1 / 2))
local notation "exteriorZeros(" τ ", " α ")" =>
  {z : {χ : PontryaginDual Cℚ // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ α ≤ |z.2.re - 1 / 2|}

/- `DirichletGRH` abbreviates the statement of `DirichletLNonvanishingRightOfHalf`
(`Statements.lean`), which a module cannot import. -/
local notation "DirichletGRH" =>
  (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0)

/-- If the finite Hecke L-function of `ψ` is the Dirichlet series of a
Dirichlet character, then under Dirichlet GRH the continued completed Hecke L-function of `ψ`
has no zero with `Re s > 1/2`. -/
private theorem order_nonpos_of_half_lt_re (hGRH : DirichletGRH) (ψ : PontryaginDual Cℚ)
    {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N}
    (hL : ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL ψ ⟨s, hs⟩ = LSeries (χ ·) s)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    meromorphicOrderAt (continuedCompletedHeckeL ψ) s ≤ 0 := by
  have hspec := continuedCompletedHeckeL_spec ψ
  by_contra hpos
  rw [not_le] at hpos
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := completedHeckeL_continuation_zeros ψ _ hspec.1 hspec.2 hs0 hpos
  have heq := meromorphicOrderAt_finiteHeckeL_continuation ψ (meromorphic_dirichletLFunction χ)
    (fun z ↦ by rw [DirichletCharacter.LFunction_eq_LSeries χ z.2, hL z.1 z.2]) hs0
  rw [← heq] at hpos
  have hne1 : s ≠ 1 := fun h ↦ by rw [h] at hs1; simp at hs1
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {1}ᶜ := fun z hz ↦
    (DirichletCharacter.differentiableAt_LFunction χ z (.inl hz)).differentiableWithinAt
  have hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s :=
    hd.analyticAt (isOpen_compl_singleton.mem_nhds hne1)
  have hzero : meromorphicOrderAt (DirichletCharacter.LFunction χ) s = 0 := by
    rw [hA.meromorphicOrderAt_eq, hA.analyticOrderAt_eq_zero.mpr (hGRH N χ s hs (.inr hne1))]
    rfl
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

/-- A positive divisor value of the continued completed Hecke L-function is a positive order. -/
private theorem order_pos_of_ord_pos (ψ : PontryaginDual Cℚ) {s : ℂ} (hs : 0 < ord(ψ, s)) :
    0 < meromorphicOrderAt (continuedCompletedHeckeL ψ) s := by
  have hspec := continuedCompletedHeckeL_spec ψ
  rw [MeromorphicOn.divisor_apply hspec.1.meromorphicOn (mem_univ s)] at hs
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (WithTop.coe_ne_top (a := (0 : ℤ))) hle)
  rw [← hn, WithTop.untop₀_coe] at hs
  rw [← hn] at hle
  exact absurd (WithTop.coe_le_coe.mp hle) (not_le.mpr hs)

/-- Under Dirichlet GRH there are no exterior zeros over ℚ, for any positive half-width.
The right half uses `order_nonpos_of_half_lt_re` for `ψ`; the left half reflects it for `ψ⁻¹`
with the project's functional equation (`introTrace_completedL_no_left_zeros`). -/
private theorem isEmpty_exteriorZeros_of_dirichletGRH (hGRH : DirichletGRH)
    (τ : ℝ≥0ˣ →ₜ* Cℚ)
    (hτ : RightInverse τ (ideleClassNorm ℚ)) {α : ℝ} (hα : 0 < α) :
    IsEmpty exteriorZeros(τ, α) := by
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨⟨⟨ψ, hψ⟩, s⟩, hord, hfar⟩ := z
  have hpos : 0 < meromorphicOrderAt (continuedCompletedHeckeL ψ) s := order_pos_of_ord_pos ψ hord
  have hψinv : ∀ t : ℝ≥0ˣ, ψ⁻¹ (τ t) = 1 := fun t ↦ by
    change (ψ (τ t))⁻¹ = 1
    rw [hψ t, inv_one]
  have hright (φ : PontryaginDual Cℚ) (hφ : ∀ t : ℝ≥0ˣ, φ (τ t) = 1) (z : ℂ)
      (hz : 1 / 2 < z.re) : meromorphicOrderAt (continuedCompletedHeckeL φ) z ≤ 0 := by
    obtain ⟨N, _, χ, -, hL⟩ :=
      exists_primitive_finiteHeckeL_eq_of_trivial_on_section τ hτ φ hφ
    exact order_nonpos_of_half_lt_re hGRH φ hL hz
  change α ≤ |s.re - 1 / 2| at hfar
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · have := introTrace_completedL_no_left_zeros ψ (fun z hz ↦ hright ψ⁻¹ hψinv z hz) s hlt
    exact absurd hpos (not_lt.mpr this)
  · rw [heq, sub_self, abs_zero] at hfar
    linarith
  · exact absurd hpos (not_lt.mpr (hright ψ hψ s hgt))

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Over ℚ, for every norm section, positive half-width
and test vanishing on the norm-one classes, the exterior zero terms sum to zero, assuming
Dirichlet GRH.
Deviation: Only F = ℚ, and Dirichlet GRH (the statement of `DirichletLNonvanishingRightOfHalf`)
is a hypothesis. The printed argument claims the cancellation unconditionally; it is the recorded
gap `traceFormula_exteriorZeros`. -/
theorem traceFormula_exteriorZeros_rat_of_dirichletGRH (hGRH : DirichletGRH)
    (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (φ : BruhatCompactSupport Cℚ) (hφ : ∀ g : C₁, φ.val g = 0) {α : ℝ} (hα : 0 < α) :
    HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0 :=
  (hasSum_exteriorZeros_iff_isEmpty τ hτ α).mpr
    (isEmpty_exteriorZeros_of_dirichletGRH hGRH τ hτ hα) φ hφ

/-- A positive zero of `L(s, χ)` of a primitive character, with `1/2 < Re s < 1`, is a zero of
positive divisor order of the completed Hecke L-function of its idelic lift. -/
private theorem ord_pos_of_LFunction_eq_zero (ψ : PontryaginDual Cℚ) {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hL : ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL ψ ⟨s, hs⟩ = LSeries (χ ·) s)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) (hz : DirichletCharacter.LFunction χ s = 0) :
    0 < ord(ψ, s) := by
  have hspec := continuedCompletedHeckeL_spec ψ
  have hm := meromorphic_dirichletLFunction χ
  have hcmp (z : ℂ) (hz0 : 0 < z.re) := meromorphicOrderAt_finiteHeckeL_continuation ψ hm
    (fun w ↦ by rw [DirichletCharacter.LFunction_eq_LSeries χ w.2, hL w.1 w.2]) hz0
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {1}ᶜ := fun z hz ↦
    (DirichletCharacter.differentiableAt_LFunction χ z (.inl hz)).differentiableWithinAt
  -- the order at 2 is 0, so the order is finite everywhere
  have h2 : meromorphicOrderAt (continuedCompletedHeckeL ψ) 2 ≠ ⊤ := by
    have hA2 : AnalyticAt ℂ (DirichletCharacter.LFunction χ) 2 :=
      hd.analyticAt (isOpen_compl_singleton.mem_nhds (by norm_num))
    have hne : DirichletCharacter.LFunction χ 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr (by norm_num)) (by norm_num)
    rw [← hcmp 2 (by norm_num), hA2.meromorphicOrderAt_eq, hA2.analyticOrderAt_eq_zero.mpr hne]
    exact ENat.map_natCast _ 0 ▸ WithTop.coe_ne_top
  have hfin : meromorphicOrderAt (continuedCompletedHeckeL ψ) s ≠ ⊤ :=
    hspec.1.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ _) (mem_univ _) h2
  -- the order at s is positive
  have hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s :=
    hd.analyticAt (isOpen_compl_singleton.mem_nhds hs1)
  have hpos : 0 < meromorphicOrderAt (continuedCompletedHeckeL ψ) s := by
    have hne : analyticOrderAt (DirichletCharacter.LFunction χ) s ≠ 0 :=
      hA.analyticOrderAt_ne_zero.mpr hz
    have hfin' : analyticOrderAt (DirichletCharacter.LFunction χ) s ≠ ⊤ := by
      intro htop
      apply hfin
      rw [← hcmp s hs0, hA.meromorphicOrderAt_eq, htop]
      rfl
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin'
    rw [← hcmp s hs0, hA.meromorphicOrderAt_eq, ← hk]
    rw [← hk] at hne
    simp only [ENat.map_natCast]
    exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast hne)
  rw [MeromorphicOn.divisor_apply hspec.1.meromorphicOn (mem_univ s)]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [← hn] at hpos ⊢
  rw [WithTop.untop₀_coe]
  exact_mod_cast hpos

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Over ℚ, the exterior-zero cancellation for every norm
section, positive half-width and test vanishing on the norm-one classes implies Dirichlet GRH.
Deviation: Only F = ℚ. This is the converse of `traceFormula_exteriorZeros_rat_of_dirichletGRH`:
any proof of the gap over ℚ proves the statement of `DirichletLNonvanishingRightOfHalf`. -/
theorem dirichletGRH_of_traceFormula_exteriorZeros_rat
    (hgap : ∀ (τ : ℝ≥0ˣ →ₜ* Cℚ) (_ : RightInverse τ (ideleClassNorm ℚ))
      (φ : BruhatCompactSupport Cℚ) (_ : ∀ g : C₁, φ.val g = 0) (α : ℝ) (_ : 0 < α),
      HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0) :
    DirichletGRH := by
  intro N _ χ s hs hguard
  rcases le_or_gt 1 s.re with h1 | h1
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hguard h1
  intro hz
  have hs1 : s ≠ 1 := fun h ↦ by rw [h] at h1; simp at h1
  -- pass to the primitive character
  have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hprim := χ.primitiveCharacter_isPrimitive
  have hz₀ : DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
    have hcl := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level
      χ.primitiveCharacter (.inr hs1)
    rw [DirichletCharacter.changeLevel_primitiveCharacter, hz] at hcl
    have hfac : ∏ p ∈ N.primeFactors,
        (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ sub_ne_zero.mpr (fun h ↦ ?_)
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      have hnorm := congrArg norm h
      rw [norm_one, norm_mul] at hnorm
      have hχ : ‖χ.primitiveCharacter p‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
      have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
        rw [Complex.norm_natCast_cpow_of_pos (Nat.prime_of_mem_primeFactors hp).pos,
          Complex.neg_re]
        exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
      nlinarith [norm_nonneg (χ.primitiveCharacter p), norm_nonneg ((p : ℂ) ^ (-s))]
    exact (mul_eq_zero.mp hcl.symm).resolve_right hfac
  -- lift to an idelic character and use the decomposition section
  obtain ⟨ψ, -, hval, hL⟩ :=
    DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hprim
  obtain ⟨e, he⟩ := ratIdeleClassGroup_decomposition
  let τ₀ : ℝ≥0ˣ →ₜ* Cℚ :=
    ⟨(e : (ℝ≥0ˣ × Uℚ) →* Cℚ).comp (MonoidHom.inl ℝ≥0ˣ Uℚ),
    e.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hτ₀ : RightInverse τ₀ (ideleClassNorm ℚ) := fun t ↦
    ideleClassNorm_decomposition e he t 1
  have hψτ : ∀ t : ℝ≥0ˣ, ψ (τ₀ t) = 1 := by
    intro t
    obtain ⟨g, hg1, hg2, hge⟩ := he t 1
    change ψ (e (t, 1)) = 1
    rw [hge]
    apply Circle.ext
    rw [hval g, coe_ideleChar, Circle.coe_one]
    have hres : resMod χ.conductor g = 1 := by
      rw [resMod_of_coords χ.conductor g t 1 hg1 hg2, residueOf_one]
    have hu : (resMod χ.conductor).toHomUnits g = 1 := Units.ext (by simp [hres])
    rw [hu, map_one, Units.val_one, inv_one]
  -- the zero is exterior for the width `Re s − 1/2`
  have hα : 0 < s.re - 1 / 2 := by linarith
  have hempty := (hasSum_exteriorZeros_iff_isEmpty τ₀ hτ₀ (s.re - 1 / 2)).mp
    (fun φ hφ ↦ hgap τ₀ hτ₀ φ hφ _ hα)
  refine hempty.false ⟨⟨⟨ψ, hψτ⟩, s⟩, ?_, ?_⟩
  · exact ord_pos_of_LFunction_eq_zero ψ hL (by linarith) hs1 hz₀
  · change s.re - 1 / 2 ≤ |s.re - 1 / 2|
    exact le_abs_self _

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Over ℚ, the exterior-zero cancellation of
`traceFormula_exteriorZeros`, with its quantifiers over norm sections, positive half-widths and
tests vanishing on the norm-one classes, holds exactly when Dirichlet GRH holds.
Deviation: Only F = ℚ. The right side is the statement of `DirichletLNonvanishingRightOfHalf`. -/
theorem traceFormula_exteriorZeros_rat_iff_dirichletGRH :
    (∀ (τ : ℝ≥0ˣ →ₜ* Cℚ) (_ : RightInverse τ (ideleClassNorm ℚ))
      (φ : BruhatCompactSupport Cℚ) (_ : ∀ g : C₁, φ.val g = 0) (α : ℝ) (_ : 0 < α),
      HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0) ↔ DirichletGRH :=
  ⟨dirichletGRH_of_traceFormula_exteriorZeros_rat,
    fun h τ hτ φ hφ _ hα ↦
      traceFormula_exteriorZeros_rat_of_dirichletGRH h τ hτ φ hφ hα⟩

/-- A finite-order character of the rational idele class group is trivial along every norm
section: every positive real is a `k`-th power. -/
private theorem trivial_on_section_of_isOfFinOrder (ψ : PontryaginDual Cℚ)
    (hψ : IsOfFinOrder ψ)
    (τ : ℝ≥0ˣ →ₜ* Cℚ) (t : ℝ≥0ˣ) : ψ (τ t) = 1 := by
  obtain ⟨k, hk, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hψ
  let r := (t : ℝ≥0) ^ ((k : ℝ)⁻¹)
  let u : ℝ≥0ˣ := Units.mk0 r (NNReal.rpow_pos (Units.zero_lt t)).ne'
  have hu : u ^ k = t := Units.ext (NNReal.rpow_inv_natCast_pow _ hk.ne')
  rw [← hu, map_pow, map_pow]
  exact (ContinuousMonoidHom.pow_apply (ψ : Cℚ →ₜ* Circle) k (τ u)).symm.trans
    (congrArg (fun η : PontryaginDual Cℚ ↦ η (τ u)) hpow)

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Over ℚ, for one fixed norm section, the exterior-zero
cancellation at the half-widths `1/(n+1)` for every test vanishing on the norm-one classes holds
exactly when Dirichlet GRH holds.
Deviation: Only F = ℚ, one section and countably many widths. The right side is the statement of
`DirichletLNonvanishingRightOfHalf`. -/
theorem traceFormula_exteriorZeros_rat_reciprocalWidths_iff_dirichletGRH
    (τ : ℝ≥0ˣ →ₜ* Cℚ)
    (hτ : RightInverse τ (ideleClassNorm ℚ)) :
    (∀ (n : ℕ) (φ : BruhatCompactSupport Cℚ), (∀ g : C₁, φ.val g = 0) →
      HasSum (fun z : exteriorZeros(τ, (1 / (n + 1 : ℝ))) ↦ zeroTerm(φ, z)) 0) ↔
      DirichletGRH := by
  refine ⟨?_, fun H n φ hφ ↦ traceFormula_exteriorZeros_rat_of_dirichletGRH H τ hτ φ hφ
    (by positivity)⟩
  intro H N _ χ s hs hguard
  rcases le_or_gt 1 s.re with h1 | h1
  · exact χ.LFunction_ne_zero_of_one_le_re hguard h1
  intro hz
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at h1
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [← χ.changeLevel_primitiveCharacter, DirichletCharacter.LFunction_changeLevel
    χ.conductor_dvd_level χ.primitiveCharacter (.inr hs1)] at hz
  obtain hz | he := mul_eq_zero.mp hz
  · obtain ⟨ψ, hfin, hL⟩ := DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq
      χ.primitiveCharacter_isPrimitive
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hs)
    have hempty := (hasSum_exteriorZeros_iff_isEmpty τ hτ (1 / (n + 1 : ℝ))).mp (H n)
    exact hempty.false ⟨⟨⟨ψ, trivial_on_section_of_isOfFinOrder ψ hfin τ⟩, s⟩,
      ord_pos_of_LFunction_eq_zero ψ hL (by linarith) hs1 hz, hn.le.trans (le_abs_self _)⟩
  · obtain ⟨p, hp, he⟩ := Finset.prod_eq_zero_iff.mp he
    have := dirichletEulerFactor_zero_re_eq_zero χ.primitiveCharacter
      (Nat.prime_of_mem_primeFactors hp) he
    linarith

end RiemannMasullo
