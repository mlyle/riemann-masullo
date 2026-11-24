module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.InfiniteAdeleRing
import RiemannMasullo.Ch01_Introduction.Sec4
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.WithSeminorms

/-! # False claims printed in §7.4 -/

@[expose] public noncomputable section

open Classical Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 150000

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "I[" F "]" => IdeleGroup (𝓞 F) F
local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "ω[" F ", " χ "]" => (χ : U[F]).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
    (ideleClassNorm F).ker →ₜ* C[F])
local notation "B" => SchwartzBergman (univ : Set ℝ)

local instance instIdeleClassT2Sec4Printed (F : Type*) [Field F] [NumberField F] :
    T2Space C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1

local instance instIdeleClassLocallyCompactSec4Printed (F : Type*) [Field F] [NumberField F] :
    LocallyCompactSpace C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

/-- Paper: Theorem 7.4.1.1(2), equation (7.4.1.1), p. 366.
The printed spectral trace evaluates the test at the unshifted zero z. Its summation
variable ρ is z + a, so the printed weight and multiplicity use ρ − a = z.
The cited §7.1.4.2 family lives in the unshifted quotient. To type the reference
for general a, use its transport by f(s) ↦ f(s+a), which gives evaluation at z−a.
At a = 0 the statement and its counterexample require no transport. -/
def Printed.spectralNuclearity_trace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)) (a : ℝ) (N : ℕ),
    0 < N → ∀ φ : BruhatCompactSupport C[F],
    let L := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    let Zeros := {z : ℂ // 0 < analyticOrderAt (L.val : ℂ → ℂ) z}
    let order := fun z : Zeros ↦ (analyticOrderAt (L.val : ℂ → ℂ) z.val).toNat
    let J := Σ z : Zeros, Fin (order z)
    let D := spectralNuclearityDenominator χ τ hτ a
    let Q := SpectralNuclearityQuotient χ τ hτ a
    ∀ (d : J → StrongDual ℂ Q) (b : J → Q),
      (∀ i f, d i (D.mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) →
      (∀ i j, d i (b j) = if i = j then 1 else 0) →
      let E := (Submodule.span ℂ (b '' {i | i.2.val < N})).topologicalClosure
      letI _instSpectralUniformSec4Printed : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
      ∃ (A : B →L[ℂ] B) (Aq : Q →L[ℂ] Q) (T : E →L[ℂ] E),
        (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) ∧
        (∀ f, Aq (D.mkQ f) = D.mkQ (A f)) ∧
        (∀ x : E, (T x).val = Aq x.val) ∧ IsStronglyNuclearOperator T ∧
        ∀ r : NuclearPresentation T, HasSum
          (fun n ↦ r.coeff n * r.functional n (r.vector n).val)
          (∑' z : Zeros, ((min N (order z) : ℕ) : ℂ) * nuclearityTestMellin χ φ z.val)

/-- Paper: Theorem 7.4.1.1(2), equation (7.4.1.1), p. 366.
Take the trivial character of a field with a multiple central zeta zero, as on
p. 529, a = 0 and N = 1. A nonzero nonnegative radial test supported at norms
between 2 and 3 has positive Mellin derivative at 1/2. The first-derivative
functional there vanishes on the printed closed span, yet takes this positive
value on the ambient image of its zeroth biorthogonal vector. -/
theorem Printed.spectralNuclearity_trace_false : ¬ Printed.spectralNuclearity_trace := by sorry

section FactorialNormalization

open Filter

/-- Paper: Theorem 7.4.1.1(2), proof following (7.4.1.2), p. 367. The printed
factorial normalization makes the retained primal biorthogonals bounded, while the
full multiplicity factorial grows at most linearly in the absolute zero height.
Here the completed divisor indexes the zeros of the character. -/
def Printed.spectralNuclearity_factorialNormalization : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)) (a : ℝ) (N : ℕ), 0 < N →
    let m := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
    let Z := {z : ℂ // 0 < m z}
    let J := Σ z : Z, Fin (min N (m z.val).toNat)
    let D := spectralNuclearityDenominator χ τ hτ a
    let Q := SpectralNuclearityQuotient χ τ hτ a
    ∃ (d : J → StrongDual ℂ Q) (b : J → Q),
      (∀ i f, d i (D.mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) ∧
      (∀ i j, d i (b j) = if i = j then 1 else 0) ∧
      Bornology.IsVonNBounded ℂ (range fun i : J ↦ (((m i.1.val).toNat.factorial : ℂ)⁻¹) • b i) ∧
      ∃ C T : ℝ, 0 < C ∧ ∀ z : Z, T ≤ |z.val.im| →
        ((m z.val).toNat.factorial : ℝ) ≤ C * |z.val.im|

local notation "ratZeroOrder" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := ℚ) 1) univ
local notation "ratWindow" => {z : ℂ // 0 < ratZeroOrder z ∧ |z.re - 1 / 2| < 1}

/-- Paper: §1.4.3, p. 29. Euler nonvanishing and reflection put all positive zeros
of the rational completed zeta function in the unit window. -/
private theorem factorialNormalization_window_infinite : Infinite ratWindow := by
  let L := continuedCompletedHeckeL (1 : U[ℚ])
  let Z := {z : ℂ // 0 < ratZeroOrder z}
  let : Infinite Z := introTrace_rat_positive_divisor_infinite
  obtain ⟨hL, hEuler⟩ := continuedCompletedHeckeL_spec (1 : U[ℚ])
  obtain ⟨ε, hε, hne, hfe⟩ :=
    completedHeckeL_continuation_functionalEquation (1 : U[ℚ]) _ _ hL hEuler hL (by simpa using hEuler)
  have hright (s : ℂ) (hs : 0 < meromorphicOrderAt L s) : s.re < 1 := by
    by_cases hr : 0 < s.re
    · exact completedHeckeL_continuation_zeros (1 : U[ℚ]) _ hL hEuler hr hs
    · linarith
  have hwindow (z : Z) : |z.val.re - 1 / 2| < (1 : ℝ) := by
    have hz := z.property
    change 0 < MeromorphicOn.divisor L univ z.val at hz
    rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)] at hz
    have hpos : 0 < meromorphicOrderAt L z.val := by
      cases he : meromorphicOrderAt L z.val with
      | top => simp
      | coe k =>
        rw [he, WithTop.untop₀_coe] at hz
        exact_mod_cast hz
    have href := meromorphicOrderAt_comp_of_deriv_ne_zero (f := L)
      (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) z.val by fun_prop)
      (show deriv (fun s : ℂ ↦ 1 - s) z.val ≠ 0 by simp)
    rw [show L ∘ (fun s : ℂ ↦ 1 - s) = ε * L from funext hfe,
      meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z.val) (hne z.val)] at href
    have hu := hright z.val hpos
    have hl := hright (1 - z.val) (href ▸ hpos)
    rw [Complex.sub_re, Complex.one_re] at hl
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  exact Infinite.of_injective (fun z : Z ↦ (⟨z.val, z.property, hwindow z⟩ : ratWindow))
    (fun _ _ h ↦ Subtype.ext (congrArg (fun w : ratWindow ↦ w.val) h))

/-- A compact rectangle contains only finitely many points of the completed divisor. -/
private theorem factorialNormalization_unbounded_height (M : ℝ) :
    ∃ z : ratWindow, M < |z.val.im| := by
  classical
  by_contra! h
  let R := |M| + 3
  let D := Metric.closedBall (0 : ℂ) R
  let L := continuedCompletedHeckeL (F := ℚ) 1
  have hmer := (continuedCompletedHeckeL_spec (F := ℚ) 1).1.meromorphicOn
  have hD : (MeromorphicOn.divisor L D).support.Finite :=
    (MeromorphicOn.divisor L D).finiteSupport (isCompact_closedBall _ _)
  let : Finite (MeromorphicOn.divisor L D).support := hD.to_subtype
  have hmem (z : ratWindow) : z.val ∈ D := by
    change z.val ∈ Metric.closedBall 0 R
    rw [Metric.mem_closedBall, dist_zero_right]
    have hs := abs_lt.mp z.property.2
    have hre : |z.val.re| ≤ 2 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by dsimp [R]; linarith [h z, le_abs_self M])
  let e (z : ratWindow) : (MeromorphicOn.divisor L D).support := ⟨z.val, by
    have hz := z.property.1.ne'
    change MeromorphicOn.divisor L D z.val ≠ 0
    rw [MeromorphicOn.divisor_apply (show MeromorphicOn L D from fun x _ ↦ hmer x (mem_univ _)) (hmem z)]
    rwa [MeromorphicOn.divisor_apply hmer (mem_univ _)] at hz⟩
  let : Infinite ratWindow := factorialNormalization_window_infinite
  let : Finite ratWindow := Finite.of_injective e fun _ _ he ↦
    Subtype.ext (congrArg (fun t : (MeromorphicOn.divisor L D).support ↦ t.val) he)
  exact not_finite ratWindow

/-- On a quotient of the entire Schwartz–Bergman space a height-square weighted family
of point evaluations in a fixed strip is bounded on every bounded set. -/
private theorem factorialNormalization_pairing {Q ι : Type*} [AddCommGroup Q] [Module ℂ Q]
    [TopologicalSpace Q] [PolynormableSpace ℂ Q]
    (π : B →L[ℂ] Q) (hπ : Topology.IsQuotientMap π) (z : ι → ℂ)
    (d : ι → StrongDual ℂ Q) (hz : ∀ i, (z i).re ∈ Icc (-1) 2)
    (heval : ∀ i f, d i (π f) = f.val (z i)) (S : Set Q) (hS : Bornology.IsVonNBounded ℂ S) :
    ∃ A : ℝ, ∀ i x, x ∈ S → ‖(z i)^2 * d i x‖ ≤ A := by
  let : BarrelledSpace ℂ B := isFrechetTVS_barrelled
    (schwartzBergman_frechet univ isOpen_univ inferInstance univ_nonempty)
  let : BarrelledSpace ℂ Q := by
    constructor
    intro q hq
    exact hπ.continuous_iff.mpr ((q.comp π.toLinearMap).continuous_of_lowerSemicontinuous
      (hq.comp π.continuous))
  let L (i : ι) := (z i)^2 • d i
  let s (i : ι) := (normSeminorm ℂ ℂ).comp (L i).toLinearMap
  have hb : BddAbove (range s) := Seminorm.bddAbove_range_iff.mpr fun x ↦ by
    obtain ⟨f, rfl⟩ := hπ.surjective x
    obtain ⟨A, hA⟩ := f.property.2.2 (-1) 2 (by norm_num) (subset_univ _) 2
    exact ⟨A, forall_mem_range.mpr fun i ↦ by
      change ‖(z i)^2 * d i (π f)‖ ≤ A
      rw [heval]
      exact hA ⟨z i, hz i, rfl⟩⟩
  have hc : Continuous (⨆ i, s i : Seminorm ℂ Q) := by
    rw [Seminorm.coe_iSup_eq hb]
    exact Seminorm.continuous_iSup s (fun i ↦ (L i).continuous.norm) hb
  obtain ⟨A, _, hA⟩ := (PolynormableSpace.withSeminorms ℂ Q).isVonNBounded_iff_seminorm_bounded.mp
    hS ⟨⨆ i, s i, hc⟩
  exact ⟨A, fun i x hx ↦ ((le_ciSup hb i : s i ≤ ⨆ j, s j) x).trans (hA x hx).le⟩

/-- Paper: Theorem 7.4.1.1(2), p. 367. Over ℚ take the trivial character, zero twist
and only the evaluation at each zero. Bounded rescaled biorthogonals would give a
quadratic lower bound on the factorials at unbounded heights; the printed bound is linear. -/
theorem Printed.spectralNuclearity_factorialNormalization_false :
    ¬ Printed.spectralNuclearity_factorialNormalization := by
  intro h
  let τ : ℝ≥0ˣ →ₜ* I[ℚ] := ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  let hτ := canonicalIdeleNormSection_rightInverse ℚ
  let D := spectralNuclearityDenominator (1 : U[ℚ]) τ hτ 0
  let Q := SpectralNuclearityQuotient (1 : U[ℚ]) τ hτ 0
  let Z := {z : ℂ // 0 < ratZeroOrder z}
  let J := Σ z : Z, Fin (min 1 (ratZeroOrder z.val).toNat)
  obtain ⟨d,b,he,hb,hS,C,T,hC,hfac⟩ := h ℚ 1 τ hτ 0 1 one_pos
  let j (z : ratWindow) : J := ⟨⟨z.val, z.property.1⟩, 0, by
    change 0 < min 1 (ratZeroOrder z.val).toNat
    have := z.property.1
    exact lt_min one_pos (by omega)⟩
  let S := range fun i : J ↦ ((ratZeroOrder i.1.val).toNat.factorial : ℂ)⁻¹ • b i
  let : PolynormableSpace ℂ B := (schwartzBergman_frechet univ isOpen_univ inferInstance univ_nonempty).2.1
  let : PolynormableSpace ℂ Q := polynormableSpace_quotient D
  obtain ⟨A,hA⟩ := factorialNormalization_pairing D.mkQL (Submodule.isQuotientMap_mkQ D)
    (fun z : ratWindow ↦ z.val) (fun z ↦ d (j z))
    (fun z ↦ by
      obtain ⟨h₁,h₂⟩ := abs_lt.mp z.property.2
      exact ⟨by linarith, by linarith⟩)
    (fun z f ↦ by simpa [j] using he (j z) f) S hS
  obtain ⟨z,hz⟩ := factorialNormalization_unbounded_height (max T (max 1 (max A 0 * C)))
  have hT := (le_max_left _ _).trans_lt hz
  have hbig := (le_max_right _ _).trans_lt hz
  have hpos : 0 < |z.val.im| := zero_lt_one.trans ((le_max_left _ _).trans_lt hbig)
  have hzbig := (le_max_right _ _).trans_lt hbig
  let m := (ratZeroOrder z.val).toNat.factorial
  have hdiag : d (j z) (b (j z)) = 1 := by simp [hb]
  have hzero : 0 < (m : ℝ) := by dsimp [m]; positivity
  have ha := hA z _ (mem_range_self (j z))
  change ‖z.val^2 * d (j z) ((m : ℂ)⁻¹ • b (j z))‖ ≤ A at ha
  rw [map_smul, hdiag, smul_eq_mul, mul_one, norm_mul, norm_pow, norm_inv,
    Complex.norm_natCast, ← div_eq_mul_inv, div_le_iff₀ hzero] at ha
  have hest : |z.val.im|^2 ≤ (max A 0 * C) * |z.val.im| := calc
    _ ≤ ‖z.val‖^2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
    _ ≤ A * m := ha
    _ ≤ max A 0 * m := by gcongr; exact le_max_left _ _
    _ ≤ max A 0 * (C * |z.val.im|) := mul_le_mul_of_nonneg_left
      (hfac ⟨z.val,z.property.1⟩ hT.le) (le_max_right _ _)
    _ = _ := by ring
  exact hzbig.not_ge ((mul_le_mul_iff_left₀ hpos).mp (by simpa [pow_two] using hest))

end FactorialNormalization

open scoped TensorProduct in
/-- Paper: Equation (7.4.3.1), p. 368.
With the displayed projective tensor topology, multiplication of the two factors
realizes the tensor product as a closed subspace of adelic Schwartz functions. -/
def Printed.archFlatProjectiveTensorEmbedding : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    let A := archimedeanFlatSchwartz (ι := {v : InfinitePlace F // v.IsReal})
      (κ := {v : InfinitePlace F // v.IsComplex})
    let V := SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F))
    ∃ e : ProjectiveTensor (↥A) V →L[ℂ] SchwartzBruhat (Multiplicative 𝔸[F]),
      IsClosedEmbedding e ∧ ∀ (h : A) (g : V) (x : 𝔸[F]),
        e (h ⊗ₜ[ℂ] g) (Multiplicative.ofAdd x) =
          h.val (fun v ↦ InfinitePlace.Completion.ringEquivRealOfIsReal v.property (x.1 v.val),
            fun v ↦ InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property (x.1 v.val)) *
          g (Multiplicative.ofAdd x.2)

open scoped TensorProduct in
/-- On a barrelled space identified with an inductive tensor product, the supremum of the
seminorms `t ↦ P j (slice of t along ε j)` is a continuous seminorm, as soon as every tensor
has only finitely many slices that are not zero. -/
private theorem archFlatProjectiveTensorEmbedding_false_seminorm
    {E V W : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [ContinuousSMul ℂ W] [BarrelledSpace ℂ W]
    (T : InductiveTensor E V ≃L[ℂ] W) (P : ℕ → Seminorm ℂ E) (hP : ∀ j, Continuous (P j))
    (ε : ℕ → V →L[ℂ] ℂ)
    (hfin : ∀ t : E ⊗[ℂ] V, ∃ N : ℕ, ∀ j, N ≤ j →
      TensorProduct.lift ((LinearMap.lsmul ℂ E).flip.compl₂ (ε j).toLinearMap) t = 0) :
    ∃ r : Seminorm ℂ W, Continuous r ∧
      ∀ (j : ℕ) (f : E) (g : V), ‖ε j g‖ * P j f ≤ r (T (f ⊗ₜ[ℂ] g)) := by
  let S (j : ℕ) : E ⊗[ℂ] V →ₗ[ℂ] E :=
    TensorProduct.lift ((LinearMap.lsmul ℂ E).flip.compl₂ (ε j).toLinearMap)
  have hS (j : ℕ) (f : E) (g : V) : S j (f ⊗ₜ[ℂ] g) = ε j g • f := by
    simp [S]
  let ρ (j : ℕ) : Seminorm ℂ (E ⊗[ℂ] V) := (P j).comp (S j)
  have hρv (j : ℕ) (f : E) (g : V) : ρ j (f ⊗ₜ[ℂ] g) = ‖ε j g‖ * P j f := by
    change P j (S j (f ⊗ₜ[ℂ] g)) = _
    rw [hS, map_smul_eq_mul]
  have hsp := withGeneratingSeminorms_spec (E ⊗[ℂ] V)
    (fun p : {p : Seminorm ℂ (E ⊗[ℂ] V) //
      (∀ x : E, Continuous (fun y : V ↦ p (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : V, Continuous (fun x : E ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)
  have hρ (j : ℕ) : @Continuous (InductiveTensor E V) ℝ _ _ (ρ j) :=
    hsp.continuous_seminorm ⟨ρ j, fun x ↦ by
      simp only [hρv]
      exact ((ε j).continuous.norm).mul continuous_const, fun y ↦ by
      simp only [hρv]
      exact continuous_const.mul (hP j)⟩
  let r (j : ℕ) : Seminorm ℂ W := (ρ j).comp T.symm.toLinearMap
  have hr (j : ℕ) : Continuous (r j) := (hρ j).comp T.symm.continuous
  have hb : BddAbove (range r) := Seminorm.bddAbove_range_iff.mpr fun w ↦ by
    obtain ⟨N, hN⟩ := hfin (T.symm w)
    refine ⟨∑ j ∈ Finset.range N, r j w, forall_mem_range.mpr fun j ↦ ?_⟩
    by_cases hj : j < N
    · exact Finset.single_le_sum (f := fun i ↦ r i w) (fun i _ ↦ apply_nonneg (r i) w)
        (Finset.mem_range.mpr hj)
    · have h0 : r j w = 0 := by
        change P j (S j (T.symm w)) = 0
        rw [show S j (T.symm w) = 0 from hN j (not_lt.mp hj), map_zero]
      rw [h0]
      exact Finset.sum_nonneg fun i _ ↦ apply_nonneg (r i) w
  refine ⟨⨆ j, r j, ?_, fun j f g ↦ ?_⟩
  · rw [Seminorm.coe_iSup_eq hb]
    exact Seminorm.continuous_iSup r hr hb
  · have h1 : r j (T (f ⊗ₜ[ℂ] g)) = ‖ε j g‖ * P j f :=
      (congrArg (ρ j) (T.symm_apply_apply (f ⊗ₜ[ℂ] g))).trans (hρv j f g)
    rw [← h1]
    exact (le_ciSup hb j : r j ≤ ⨆ i, r i) _

/-- Every neighbourhood of zero in the flat archimedean Schwartz space of `ℚ` contains
functions with arbitrarily large weighted supremum of one fixed order: a neighbourhood controls
finitely many weights, and spreading a fixed bump out beats the next one. -/
private theorem archFlatProjectiveTensorEmbedding_false_unbounded
    (U : Set (archimedeanFlatSchwartz (ι := {v : InfinitePlace ℚ // v.IsReal})
      (κ := {v : InfinitePlace ℚ // v.IsComplex})))
    (hU : U ∈ 𝓝 0) :
    ∃ j : ℕ, ∀ M : ℝ, ∃ a ∈ U, M ≤ SchwartzMap.seminorm ℂ j 0 a.val := by
  let Coord := ({v : InfinitePlace ℚ // v.IsReal} → ℝ) × ({v : InfinitePlace ℚ // v.IsComplex} → ℂ)
  obtain ⟨u, hu, hsub⟩ := (mem_nhds_subtype _ _ _).mp hU
  obtain ⟨s, δ, hδ, hball⟩ := ((schwartz_withSeminorms ℂ Coord ℂ).mem_nhds_iff _ _).mp hu
  let c : Coord := (fun _ ↦ 1, fun _ ↦ 1)
  let b : ContDiffBump c := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let bc : Coord → ℂ := fun x ↦ ((b x : ℝ) : ℂ)
  have hbc : ContDiff ℝ (⊤ : ℕ∞) bc := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hbs : HasCompactSupport bc := b.hasCompactSupport.comp_left Complex.ofReal_zero
  let h₁ : SchwartzMap Coord ℂ := hbs.toSchwartzMap hbc
  have hc1 : (1 : ℝ) ≤ ‖c‖ := by
    let i₀ : {v : InfinitePlace ℚ // v.IsReal} := ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
    have h3 : ‖c.1 i₀‖ ≤ ‖c‖ := (norm_le_pi_norm _ i₀).trans (norm_fst_le _)
    have h4 : ‖c.1 i₀‖ = 1 := norm_one
    linarith
  let K := s.sup Prod.fst
  let C : ℝ := (∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 h₁) + 1
  have hC : 0 < C :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ ↦ apply_nonneg _ _) one_pos
  refine ⟨K + 1, fun M ↦ ?_⟩
  let μ : ℝ := max 1 (2 * C * M / δ)
  have hμ1 : 1 ≤ μ := le_max_left _ _
  have hμ0 : 0 < μ := zero_lt_one.trans_le hμ1
  let L : Coord ≃L[ℝ] Coord := ContinuousLinearEquiv.equivOfInverse
    (μ⁻¹ • ContinuousLinearMap.id ℝ Coord) (μ • ContinuousLinearMap.id ℝ Coord)
    (fun x ↦ by simp [smul_smul, hμ0.ne']) (fun x ↦ by simp [smul_smul, hμ0.ne'])
  have hL (x : Coord) : L x = μ⁻¹ • x := rfl
  let hd : SchwartzMap Coord ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L h₁
  have hdv (x : Coord) : hd x = bc (μ⁻¹ • x) := rfl
  have hLn : ‖(L : Coord →L[ℝ] Coord)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
    change ‖μ⁻¹ • x‖ ≤ 1 * ‖x‖
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hμ0.le)]
    exact mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hμ1) (norm_nonneg x)
  have hsem (i : ℕ × ℕ) (hi : i ∈ s) :
      SchwartzMap.seminorm ℂ i.1 i.2 hd ≤ μ ^ K * C := by
    refine SchwartzMap.seminorm_le_bound ℂ i.1 i.2 hd (by positivity) fun x ↦ ?_
    have hder : iteratedFDeriv ℝ i.2 (hd : Coord → ℂ) x =
        (iteratedFDeriv ℝ i.2 (h₁ : Coord → ℂ) (L x)).compContinuousLinearMap
          fun _ ↦ (L : Coord →L[ℝ] Coord) :=
      (L : Coord →L[ℝ] Coord).iteratedFDeriv_comp_right (h₁.smooth ⊤) x (mod_cast le_top)
    have hn : ‖iteratedFDeriv ℝ i.2 (hd : Coord → ℂ) x‖ ≤
        ‖iteratedFDeriv ℝ i.2 (h₁ : Coord → ℂ) (L x)‖ := by
      rw [hder]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      rw [Finset.prod_const]
      exact pow_le_one₀ (norm_nonneg _) hLn
    have hx : ‖x‖ = μ * ‖L x‖ := by
      rw [hL, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hμ0.le), mul_inv_cancel_left₀ hμ0.ne']
    have hk : i.1 ≤ K := Finset.le_sup (f := Prod.fst) hi
    calc ‖x‖ ^ i.1 * ‖iteratedFDeriv ℝ i.2 (hd : Coord → ℂ) x‖
        ≤ (μ * ‖L x‖) ^ i.1 * ‖iteratedFDeriv ℝ i.2 (h₁ : Coord → ℂ) (L x)‖ := by
          rw [hx]
          exact mul_le_mul_of_nonneg_left hn (by positivity)
      _ = μ ^ i.1 * (‖L x‖ ^ i.1 * ‖iteratedFDeriv ℝ i.2 (h₁ : Coord → ℂ) (L x)‖) := by
          rw [mul_pow, mul_assoc]
      _ ≤ μ ^ K * (SchwartzMap.seminorm ℂ i.1 i.2 h₁) :=
          mul_le_mul (pow_le_pow_right₀ hμ1 hk) (SchwartzMap.le_seminorm ℂ i.1 i.2 h₁ (L x))
            (by positivity) (by positivity)
      _ ≤ μ ^ K * C := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (Finset.single_le_sum (f := fun i : ℕ × ℕ ↦ SchwartzMap.seminorm ℂ i.1 i.2 h₁)
            (fun i _ ↦ apply_nonneg _ _) hi).trans (le_add_of_nonneg_right zero_le_one)
  let t : ℝ := δ / (2 * C * μ ^ K)
  have ht : 0 < t := by positivity
  have hflat : hd ∈ archimedeanFlatSchwartz (ι := {v : InfinitePlace ℚ // v.IsReal})
      (κ := {v : InfinitePlace ℚ // v.IsComplex}) := by
    apply mem_archimedeanFlatSchwartz_of_tsupport
    rw [Set.disjoint_left]
    intro x hx hw
    have hx1 : L x ∈ tsupport bc := by
      have h9 := tsupport_comp_eq_preimage bc L.toHomeomorph
      exact (Set.ext_iff.mp h9 x).mp hx
    have hx2 : L x ∈ Metric.closedBall c (1 / 2) := by
      have h10 : tsupport bc ⊆ tsupport (b : Coord → ℝ) :=
        tsupport_comp_subset Complex.ofReal_zero _
      rw [b.tsupport_eq] at h10
      exact h10 hx1
    rw [Metric.mem_closedBall, dist_eq_norm] at hx2
    rcases hw with ⟨i, hi⟩ | ⟨j, hj⟩
    · have h1 : ‖(L x - c).1 i‖ ≤ ‖L x - c‖ := (norm_le_pi_norm _ i).trans (norm_fst_le _)
      have h2 : (L x - c).1 i = -1 := by
        change μ⁻¹ • x.1 i - 1 = -1
        rw [hi, smul_zero, zero_sub]
      rw [h2, norm_neg, norm_one] at h1
      linarith
    · have h1 : ‖(L x - c).2 j‖ ≤ ‖L x - c‖ := (norm_le_pi_norm _ j).trans (norm_snd_le _)
      have h2 : (L x - c).2 j = -1 := by
        change μ⁻¹ • x.2 j - 1 = -1
        rw [hj, smul_zero, zero_sub]
      rw [h2, norm_neg, norm_one] at h1
      linarith
  refine ⟨⟨(t : ℂ) • hd, Submodule.smul_mem _ _ hflat⟩, hsub (hball ?_), ?_⟩
  · change (s.sup (schwartzSeminormFamily ℂ Coord ℂ)) ((t : ℂ) • hd - 0) < δ
    rw [sub_zero]
    refine Seminorm.finset_sup_apply_lt hδ fun i hi ↦ ?_
    change SchwartzMap.seminorm ℂ i.1 i.2 ((t : ℂ) • hd) < δ
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    calc t * SchwartzMap.seminorm ℂ i.1 i.2 hd ≤ t * (μ ^ K * C) :=
          mul_le_mul_of_nonneg_left (hsem i hi) ht.le
      _ = δ / 2 := by
          simp only [t]
          field_simp
      _ < δ := half_lt_self hδ
  · change M ≤ SchwartzMap.seminorm ℂ (K + 1) 0 ((t : ℂ) • hd)
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    have hval : hd (μ • c) = 1 := by
      rw [hdv, smul_smul, inv_mul_cancel₀ hμ0.ne', one_smul]
      change ((b c : ℝ) : ℂ) = 1
      rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), Complex.ofReal_one]
    have hlow := SchwartzMap.norm_pow_mul_le_seminorm ℂ hd (K + 1) (μ • c)
    rw [hval, norm_one, mul_one, norm_smul, Real.norm_of_nonneg hμ0.le] at hlow
    have h5 : μ ^ (K + 1) ≤ (μ * ‖c‖) ^ (K + 1) :=
      pow_le_pow_left₀ hμ0.le (le_mul_of_one_le_right hμ0.le hc1) _
    have h6 : M ≤ t * μ ^ (K + 1) := by
      have h7 : 2 * C * M / δ ≤ μ := le_max_right _ _
      have h8 : t * μ ^ (K + 1) = δ * μ / (2 * C) := by
        simp only [t]
        field_simp
        ring
      rw [h8, le_div_iff₀ (by positivity)]
      have h9 := (div_le_iff₀ hδ).mp h7
      linarith
    exact h6.trans (mul_le_mul_of_nonneg_left (h5.trans hlow) ht.le)

/-- Points of the finite adeles of `ℚ` leaving every compact set at one place: the negative
powers of a uniformizer there and one elsewhere. -/
private theorem archFlatProjectiveTensorEmbedding_false_points :
    ∃ (v₀ : HeightOneSpectrum (𝓞 ℚ)) (y : ℕ → FiniteAdeleRing (𝓞 ℚ) ℚ),
      ∀ K : Set (v₀.adicCompletion ℚ), IsCompact K → ∃ N : ℕ, ∀ j, N ≤ j → y j v₀ ∉ K := by
  let v₀ : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨3, Nat.prime_three⟩
  have hU := (Valued.v : Valuation (v₀.adicCompletion ℚ)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : v₀.adicCompletion ℚ := hU.choose
  have hπ := hU.choose_spec
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπ1 : ‖π‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hπ.val_lt_one
  let y (j : ℕ) : FiniteAdeleRing (𝓞 ℚ) ℚ :=
    RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 ℚ) ↦ w.adicCompletionIntegers ℚ)
      v₀ (π⁻¹ ^ j)
  refine ⟨v₀, y, fun K hK ↦ ?_⟩
  obtain ⟨M, hM⟩ := (hK.image continuous_norm).bddAbove
  have hgt : 1 < ‖π‖⁻¹ := (one_lt_inv₀ (norm_pos_iff.mpr hπ0)).mpr hπ1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop M)
  refine ⟨N, fun j hj hmem ↦ ?_⟩
  have h2 : y j v₀ = π⁻¹ ^ j := RestrictedProduct.mulSingle_eq_same _ _ _
  have h3 := hM (Set.mem_image_of_mem _ hmem)
  rw [h2, norm_pow, norm_inv] at h3
  exact (hN j hj).not_ge h3

open scoped TensorProduct in
/-- For points of the finite adeles leaving every compact set at one place, every tensor of
adelic factors has only finitely many slices at these points that are not zero: an adelic
Schwartz–Bruhat function is a finite sum of archimedean functions times indicators of compact
rectangles. -/
private theorem archFlatProjectiveTensorEmbedding_false_slices
    (T : InductiveTensor (SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)))
        (SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 ℚ) ℚ))) ≃L[ℂ]
      SchwartzBruhat (Multiplicative 𝔸[ℚ]))
    (hT : ∀ (f : SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)))
      (g : SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 ℚ) ℚ))) (x : 𝔸[ℚ]),
      T (f ⊗ₜ[ℂ] g) (Multiplicative.ofAdd x) =
        f (Multiplicative.ofAdd x.1) * g (Multiplicative.ofAdd x.2))
    (v₀ : HeightOneSpectrum (𝓞 ℚ)) (y : ℕ → FiniteAdeleRing (𝓞 ℚ) ℚ)
    (hy : ∀ K : Set (v₀.adicCompletion ℚ), IsCompact K → ∃ N : ℕ, ∀ j, N ≤ j → y j v₀ ∉ K)
    (ε : ℕ → SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 ℚ) ℚ)) →L[ℂ] ℂ)
    (hε : ∀ j g, ε j g = g (Multiplicative.ofAdd (y j)))
    (t : SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)) ⊗[ℂ]
      SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 ℚ) ℚ))) :
    ∃ N : ℕ, ∀ j, N ≤ j → TensorProduct.lift ((LinearMap.lsmul ℂ
      (SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)))).flip.compl₂ (ε j).toLinearMap) t =
        0 := by
  have hslice (j : ℕ) (s : SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)) ⊗[ℂ]
      SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 ℚ) ℚ))) (x : InfiniteAdeleRing ℚ) :
      TensorProduct.lift ((LinearMap.lsmul ℂ
        (SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)))).flip.compl₂ (ε j).toLinearMap) s
          (Multiplicative.ofAdd x) = T s (Multiplicative.ofAdd ((x, y j) : 𝔸[ℚ])) := by
    induction s using TensorProduct.inductionOn with
    | tmul f g =>
      rw [TensorProduct.lift.tmul, hT]
      change (ε j g • f) (Multiplicative.ofAdd x) = _
      rw [SchwartzBruhat.coe_smul, hε]
      exact mul_comm _ _
    | add a b ha hb =>
      have h1 : T (a + b) = T a + T b := map_add T a b
      rw [map_add, h1, SchwartzBruhat.coe_add, SchwartzBruhat.coe_add, Pi.add_apply,
        Pi.add_apply, ha, hb]
  obtain ⟨r, c, arch, K, φ, -, hφ, hΦ⟩ :=
    adeleSchwartz_eq_sum_compactOpen_rectangles (F := ℚ) (T t)
  choose N hN using fun i ↦ hy (K i v₀) ((hφ i).1 v₀).1
  refine ⟨Finset.univ.sup N, fun j hj ↦ SchwartzBruhat.ext fun z ↦ ?_⟩
  have hz : z = Multiplicative.ofAdd (Multiplicative.toAdd z) := rfl
  rw [hz, hslice, hΦ, SchwartzBruhat.coe_zero, Pi.zero_apply]
  let ev : SchwartzBruhat (Multiplicative 𝔸[ℚ]) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (Multiplicative.ofAdd ((Multiplicative.toAdd z, y j) : 𝔸[ℚ]))).comp
      ((schwartzBruhatSubmodule (Multiplicative 𝔸[ℚ])).subtype.comp
        (SchwartzBruhat.toSubmodule (Multiplicative 𝔸[ℚ])).toLinearMap)
  change ev (∑ i, c i • φ i) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [map_smul]
  change c i • φ i (Multiplicative.ofAdd ((Multiplicative.toAdd z, y j) : 𝔸[ℚ])) = 0
  rw [(hφ i).2.2, Set.indicator_of_notMem, mul_zero, smul_zero]
  intro hmem
  exact hN i j ((Finset.le_sup (Finset.mem_univ i)).trans hj) (hmem v₀)

open scoped TensorProduct RestrictedProduct in
/-- Paper: Equation (7.4.3.1), p. 368.
Over ℚ choose a basis of the finite test space and flat real functions supported
in (2,3). In the ambient locally convex direct sum one continuous seminorm can
use derivative order j on basis coordinate j. Projective continuity would
bound all those orders by one continuous archimedean seminorm with a separate
constant per coordinate. A fixed bump times exp(i n x) contradicts this bound. -/
theorem Printed.archFlatProjectiveTensorEmbedding_false :
    ¬ Printed.archFlatProjectiveTensorEmbedding := by
  intro hP
  obtain ⟨e, -, he⟩ := hP ℚ
  obtain ⟨T, hT⟩ := adeleSchwartz_inductiveTensor_equiv ℚ
  obtain ⟨J, hJ⟩ := archimedeanSchwartzBruhat_equiv (F := ℚ)
  obtain ⟨v₀, y, hy⟩ := archFlatProjectiveTensorEmbedding_false_points
  let : Fact (∀ v : HeightOneSpectrum (𝓞 ℚ),
      IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let (v : HeightOneSpectrum (𝓞 ℚ)) : CompactSpace (v.adicCompletionIntegers ℚ) :=
    compactSpace_adicCompletionIntegers v
  let : LocallyCompactSpace (Multiplicative (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    change LocallyCompactSpace (Πʳ v : HeightOneSpectrum (𝓞 ℚ),
      [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ])
    infer_instance
  let : T2Space (Multiplicative (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    change T2Space (Πʳ v : HeightOneSpectrum (𝓞 ℚ),
      [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ])
    infer_instance
  -- Point evaluations at the `y j`, and functions equal to one there.
  choose ε hε' using fun j : ℕ ↦ schwartzBruhat_dirac_support (Multiplicative.ofAdd (y j))
  have hε (j : ℕ) (f : SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 ℚ) ℚ))) :
      ε j f = f (Multiplicative.ofAdd (y j)) := (hε' j).1 f
  have hne (j : ℕ) : ∃ f : SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 ℚ) ℚ)),
      f (Multiplicative.ofAdd (y j)) ≠ 0 := by
    by_contra! h
    have hx : Multiplicative.ofAdd (y j) ∈ schwartzBruhatVanishingLocus (ε j) :=
      Set.mem_sUnion.mpr ⟨Set.univ, ⟨isOpen_univ, fun f _ ↦ (hε j f).trans (h f)⟩,
        Set.mem_univ _⟩
    rw [(hε' j).2.1] at hx
    exact hx (Set.mem_singleton _)
  choose f₀ hf₀ using hne
  let g (j : ℕ) : SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
    (f₀ j (Multiplicative.ofAdd (y j)))⁻¹ • f₀ j
  have hg (j : ℕ) : g j (Multiplicative.ofAdd (y j)) = 1 := by
    change ((f₀ j (Multiplicative.ofAdd (y j)))⁻¹ • f₀ j) (Multiplicative.ofAdd (y j)) = 1
    rw [SchwartzBruhat.coe_smul, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ (hf₀ j)]
  let P (j : ℕ) : Seminorm ℂ (SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))) :=
    (SchwartzMap.seminorm ℂ j 0).comp J.symm.toLinearMap
  have hPc (j : ℕ) : Continuous (P j) :=
    ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (j, 0)).comp J.symm.continuous
  have hbar : BarrelledSpace ℂ (SchwartzBruhat (Multiplicative 𝔸[ℚ])) := (adeleSchwartz_montel ℚ).2.1
  obtain ⟨r, hr, hrl⟩ := archFlatProjectiveTensorEmbedding_false_seminorm T P hPc ε
    (archFlatProjectiveTensorEmbedding_false_slices T hT v₀ y hy ε hε)
  let : PolynormableSpace ℂ (SchwartzMap (({v : InfinitePlace ℚ // v.IsReal} → ℝ) ×
      ({v : InfinitePlace ℚ // v.IsComplex} → ℂ)) ℂ) :=
    (schwartz_withSeminorms ℂ _ ℂ).toPolynormableSpace
  let : T2Space (SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 ℚ) ℚ))) :=
    schwartzBruhat_t2_of_stages
  have hβ := (continuous_projectiveTensor_iff e.toLinearMap).mp e.continuous
  have hsmall := (hr.comp hβ).continuousAt.preimage_mem_nhds
    (x := 0) (t := Iio 1) (Iio_mem_nhds (lt_of_eq_of_lt ((congrArg r ((congrArg e
      (TensorProduct.zero_tmul _ _)).trans (map_zero e))).trans (map_zero r)) one_pos))
  obtain ⟨U, hU, U', hU', hUU'⟩ := mem_nhds_prod_iff.mp hsmall
  obtain ⟨j, hj⟩ := archFlatProjectiveTensorEmbedding_false_unbounded U hU
  obtain ⟨c, hc, hc0⟩ := ((absorbent_nhds_zero (𝕜 := ℂ) hU').eventually_nhdsNE_zero (g j)
    |>.and eventually_mem_nhdsWithin).exists
  obtain ⟨a, haU, ha⟩ := hj (1 / ‖c‖)
  have h1 : r (e (a ⊗ₜ[ℂ] (c • g j))) < 1 := hUU' (show (a, c • g j) ∈ U ×ˢ U' from ⟨haU, hc⟩)
  have h2 : e (a ⊗ₜ[ℂ] (c • g j)) = T (J a.val ⊗ₜ[ℂ] (c • g j)) :=
    SchwartzBruhat.ext fun z ↦ by
      have hz : z = Multiplicative.ofAdd (Multiplicative.toAdd z) := rfl
      rw [hz, he, hT, hJ]
      rfl
  have h3 := hrl j (J a.val) (c • g j)
  rw [← h2] at h3
  have h4 : ε j (c • g j) = c := by rw [map_smul, hε, hg, smul_eq_mul, mul_one]
  have h5 : P j (J a.val) = SchwartzMap.seminorm ℂ j 0 a.val :=
    congrArg (SchwartzMap.seminorm ℂ j 0) (J.symm_apply_apply a.val)
  rw [h4, h5] at h3
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have h6 := (div_le_iff₀' hcpos).mp ha
  linarith

/-- Paper: Theorem 7.4.3.1(1), p. 368.
The theta image of the printed unrestricted archimedean-flat tests is a nonzero
closed subspace contained in the zero-moment theta image. -/
def Printed.archNuclearityDenominator_nonzero_closed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]),
    let q := (LinearMap.ker (homogeneousAdelicThetaLinearMap F (ω[F, χ]))).mkQ
    let D := (globalArchimedeanFlatTests F).map q
    D ≠ ⊥ ∧ IsClosed (D : Set (GlobalHomogeneousThetaSpace F (ω[F, χ]))) ∧
      D ≤ globalPolarFreeThetaSubmodule (ω[F, χ])

open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- The indicator of a compact open subgroup is a Schwartz–Bruhat function. -/
private theorem archNuclearityDenominator_indicator_mem {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup G) (hO : IsOpen (H : Set G)) (hK : IsCompact (H : Set G)) :
    (fun x : G ↦ if x ∈ H then (1 : ℂ) else 0) ∈ schwartzBruhatSubmodule G := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hK
  let : CompactSpace (lcaAnnihilator H) :=
    isCompact_iff_compactSpace.1 (isCompact_lcaAnnihilator H hO)
  let a : BruhatStructuralPair G :=
    ⟨⟨H, OrderDual.toDual H⟩, hO, isCompactlyGeneratedGroup_of_compact,
      ⟨H.isClosed_of_isOpen hO, isOpen_lcaAnnihilator H hK,
        (show IsCompactlyGeneratedGroup (lcaAnnihilator H) from
          isCompactlyGeneratedGroup_of_compact)⟩, le_rfl⟩
  have hsub : Subsingleton a.quotient := by
    refine ⟨fun x y ↦ ?_⟩
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    exact QuotientGroup.eq.mpr (by
      change ((x⁻¹ * y : H) : G) ∈ H
      exact (x⁻¹ * y).property)
  let Z := ElementaryLieGroup 0 0 0 (Fin 1)
  have hZ : Subsingleton Z := by
    change Subsingleton (EuclideanSpace ℝ (Fin 0) × (Fin 0 → AddCircle (1 : ℝ)) ×
      (Fin 0 → ℤ) × Fin 1)
    infer_instance
  let j : a.quotient ≃* Multiplicative Z :=
    { toFun := fun _ ↦ 1
      invFun := fun _ ↦ 1
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ @Subsingleton.elim _ hZ _ _
      map_mul' := fun _ _ ↦ (mul_one 1).symm }
  let e : ElementaryLCAPresentation a.quotient :=
    { realDim := 0, torusDim := 0, latticeRank := 0, finiteFactor := Fin 1
      equiv := j.toContinuousMulEquiv (fun S ↦ by
        rcases S.eq_empty_or_nonempty with h | h
        · subst h; simp
        · have : S = univ := by
            obtain ⟨z, hz⟩ := h
            exact eq_univ_of_forall fun w ↦ (@Subsingleton.elim _ hZ w z) ▸ hz
          subst this; simp) }
  let g : Z → ℂ := fun _ ↦ 1
  have hg : g ∈ elementarySchwartzSubmodule 0 0 0 (Fin 1) := by
    refine ⟨fun z b ↦ contDiff_const, fun i ↦ ?_⟩
    rw [Subsingleton.elim i (0, 0, 0, 0), elementarySchwartzBound_zero]
    simp [g]
  let s : SchwartzBruhatStage e := ⟨g, hg⟩
  apply Submodule.mem_iSup_of_mem a
  apply Submodule.mem_iSup_of_mem e
  refine ⟨s, funext fun x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply]
  by_cases hx : x ∈ H
  · have hx' : x ∈ a.val.1 := hx
    simp [hx, hx', s, g]
  · have hx' : x ∉ a.val.1 := hx
    simp [hx, hx']



open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- The integral finite adeles form a compact open additive subgroup. -/
private def archNuclearityDenominator_integralSubgroup (F : Type) [Field F] [NumberField F] :
    Subgroup (Multiplicative (FiniteAdeleRing (𝓞 F) F)) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 F),
    (Multiplicative.toAdd x) v ∈ v.adicCompletionIntegers F}
  mul_mem' {a b} ha hb v := by
    change (Multiplicative.toAdd a + Multiplicative.toAdd b) v ∈ _
    exact add_mem (ha v) (hb v)
  one_mem' v := by
    change (0 : FiniteAdeleRing (𝓞 F) F) v ∈ _
    exact zero_mem _
  inv_mem' {a} ha v := by
    change (- Multiplicative.toAdd a) v ∈ _
    exact neg_mem (ha v)

open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- The integral finite adeles are open. -/
private theorem archNuclearityDenominator_integralSubgroup_isOpen (F : Type) [Field F]
    [NumberField F] :
    IsOpen (archNuclearityDenominator_integralSubgroup F : Set (Multiplicative (FiniteAdeleRing (𝓞 F) F))) := by
  let : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  exact RestrictedProduct.isOpen_forall_mem Fact.out

open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- The integral finite adeles are compact. -/
private theorem archNuclearityDenominator_integralSubgroup_isCompact (F : Type) [Field F]
    [NumberField F] :
    IsCompact (archNuclearityDenominator_integralSubgroup F : Set (Multiplicative (FiniteAdeleRing (𝓞 F) F))) := by
  let (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F)
    (A := fun v ↦ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- The indicator of the integral finite adeles is a Schwartz–Bruhat function. -/
private theorem archNuclearityDenominator_finiteIndicator_mem (F : Type) [Field F]
    [NumberField F] :
    (fun x : Multiplicative (FiniteAdeleRing (𝓞 F) F) ↦
      if x ∈ archNuclearityDenominator_integralSubgroup F then (1 : ℂ) else 0) ∈
      schwartzBruhatSubmodule (Multiplicative (FiniteAdeleRing (𝓞 F) F)) := by
  let : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let : LocallyCompactSpace (Multiplicative (FiniteAdeleRing (𝓞 F) F)) := by
    change LocallyCompactSpace (Πʳ v : HeightOneSpectrum (𝓞 F),
      [v.adicCompletion F, v.adicCompletionIntegers F])
    infer_instance
  let : IsTopologicalGroup (Multiplicative (FiniteAdeleRing (𝓞 F) F)) := inferInstance
  let : T2Space (Multiplicative (FiniteAdeleRing (𝓞 F) F)) := by
    change T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
      [v.adicCompletion F, v.adicCompletionIntegers F])
    infer_instance
  exact archNuclearityDenominator_indicator_mem _
    (archNuclearityDenominator_integralSubgroup_isOpen F)
    (archNuclearityDenominator_integralSubgroup_isCompact F)



open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- Over any number field there is an archimedean-flat adelic tensor whose Fourier value at
the origin is nonzero: a nonnegative bump away from the coordinate walls times the indicator
of the integral finite adeles. -/
private theorem archNuclearityDenominator_flat_fourier_ne_zero (F : Type) [Field F]
    [NumberField F] :
    ∃ f ∈ globalArchimedeanFlatTests F,
      adeleSchwartzFourier (F := F) f (Multiplicative.ofAdd 0) ≠ 0 := by
  let Coord := ({v : InfinitePlace F // v.IsReal} → ℝ) × ({v : InfinitePlace F // v.IsComplex} → ℂ)
  let c : Coord := (fun _ ↦ 1, fun _ ↦ 1)
  let b : ContDiffBump c := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let bc : Coord → ℂ := fun u ↦ ((b u : ℝ) : ℂ)
  have hbc : ContDiff ℝ (⊤ : ℕ∞) bc := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hbs : HasCompactSupport bc := b.hasCompactSupport.comp_left Complex.ofReal_zero
  let h₀ : SchwartzMap Coord ℂ := hbs.toSchwartzMap hbc
  have hflat : h₀ ∈ archimedeanFlatSchwartz (ι := {v : InfinitePlace F // v.IsReal})
      (κ := {v : InfinitePlace F // v.IsComplex}) := by
    apply mem_archimedeanFlatSchwartz_of_tsupport
    rw [Set.disjoint_left]
    intro u hu hw
    have hu' : u ∈ Metric.closedBall c (1 / 2) := by
      have : tsupport (h₀ : Coord → ℂ) ⊆ tsupport (b : Coord → ℝ) :=
        tsupport_comp_subset Complex.ofReal_zero _
      rw [b.tsupport_eq] at this
      exact this hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu'
    rcases hw with ⟨i, hi⟩ | ⟨j, hj⟩
    · have h1 : ‖(u - c).1 i‖ ≤ ‖u - c‖ := (norm_le_pi_norm _ i).trans (norm_fst_le _)
      have h2 : (u - c).1 i = -1 := by
        change u.1 i - 1 = -1
        rw [hi]; ring
      rw [h2] at h1
      norm_num at h1
      linarith
    · have h1 : ‖(u - c).2 j‖ ≤ ‖u - c‖ := (norm_le_pi_norm _ j).trans (norm_snd_le _)
      have h2 : (u - c).2 j = -1 := by
        change u.2 j - 1 = -1
        rw [hj]; ring
      rw [h2] at h1
      norm_num at h1
      linarith
  have hinf := (mem_archimedeanSchwartzBruhat_iff (F := F)
    (fun x ↦ h₀ (InfiniteAdeleRing.ringEquiv_mixedSpace F x))).mpr ⟨h₀, fun _ ↦ rfl⟩
  let fI : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) := ⟨_, hinf⟩
  let H := archNuclearityDenominator_integralSubgroup F
  let g : SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F)) :=
    ⟨_, archNuclearityDenominator_finiteIndicator_mem F⟩
  let tensor := (adeleSchwartz_inductiveTensor_equiv F).choose
  let test := tensor (fI ⊗ₜ[ℂ] g)
  refine ⟨test, Submodule.subset_span ⟨fI, g, ⟨h₀, hflat⟩, fun _ ↦ rfl, fun h ↦ h.elim, rfl⟩, ?_⟩
  let R : 𝔸[F] → ℝ := fun x ↦ b (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) *
    (if Multiplicative.ofAdd x.2 ∈ H then 1 else 0)
  have hR : ∀ x : 𝔸[F], test (Multiplicative.ofAdd x) = (R x : ℂ) := by
    intro x
    rw [(adeleSchwartz_inductiveTensor_equiv F).choose_spec fI g x]
    change bc _ * (if Multiplicative.ofAdd x.2 ∈ H then (1 : ℂ) else 0) = _
    simp only [R, bc]
    split_ifs <;> simp
  let : MeasurableSpace 𝔸[F] := borel _
  obtain ⟨hint, hval⟩ := adeleSchwartzFourier_apply_zero test
  rw [hval]
  have hfun : (fun x : 𝔸[F] ↦ test (Multiplicative.ofAdd x)) = fun x ↦ (R x : ℂ) := funext hR
  rw [hfun] at hint ⊢
  rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
  have hRint : Integrable R (additiveTamagawaMeasure F) := by
    simpa using hint.re
  have hR0 : 0 ≤ R := fun x ↦ mul_nonneg b.nonneg (by split_ifs <;> norm_num)
  refine ne_of_gt ((integral_pos_iff_support_of_nonneg hR0 hRint).mpr ?_)
  let U : Set 𝔸[F] := (fun x : 𝔸[F] ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) ⁻¹'
      Metric.ball c (1 / 2) ∩ (fun x : 𝔸[F] ↦ Multiplicative.ofAdd x.2) ⁻¹' (H : Set _)
  have hU : IsOpen U := by
    refine IsOpen.inter (Metric.isOpen_ball.preimage ?_)
      ((archNuclearityDenominator_integralSubgroup_isOpen F).preimage ?_)
    · exact (continuous_infiniteAdeleRingEquivMixedSpace F).comp continuous_fst
    · exact continuous_ofAdd.comp continuous_snd
  have hUne : U.Nonempty := by
    refine ⟨((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm c, 0), ?_, ?_⟩
    · change InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm c) ∈ Metric.ball c (1 / 2)
      rw [RingEquiv.apply_symm_apply]
      exact Metric.mem_ball_self (by norm_num)
    · exact H.one_mem
  have hUsupp : U ⊆ Function.support R := by
    intro x hx
    have h1 : 0 < b (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) := b.pos_of_mem_ball hx.1
    have h2 : Multiplicative.ofAdd x.2 ∈ H := hx.2
    simp only [Function.mem_support, R, h2, ↓reduceIte, mul_one]
    exact h1.ne'
  have hμ : (additiveTamagawaMeasure F).IsAddHaarMeasure :=
    (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  have hpos := hU.measure_pos (additiveTamagawaMeasure F) hUne
  exact hpos.trans_le (measure_mono hUsupp)


open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- The norm-one idele classes have positive Tamagawa mass. -/
private theorem archNuclearityDenominator_volume_pos (F : Type) [Field F] [NumberField F] :
    0 < (normOneIdeleClassTamagawaMeasure F univ).toReal := by
  rw [normOneIdeleClassTamagawaMeasure_volume]
  have := NumberField.classNumber_pos F
  have := NumberField.Units.regulator_pos F
  have := NumberField.Units.torsionOrder_pos F
  have := Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
  exact ENNReal.toReal_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top


open MeasureTheory Filter in
open scoped RestrictedProduct ContDiff TensorProduct in
/-- For the trivial norm-one character, equal homogeneous theta functions force equal Fourier
values at the origin, once both tests vanish at the origin and the second Fourier value is zero.
The polar term `|x|⁻¹ f̂(0)` blows up at small norm while the theta difference decays. -/
private theorem archNuclearityDenominator_fourier_eq_zero (F : Type) [Field F] [NumberField F]
    (ω₁ : PontryaginDual (ideleClassNorm F).ker) (hω : ω₁ = 1)
    (f g : SchwartzBruhat (Multiplicative 𝔸[F]))
    (hθ : homogeneousAdelicThetaLinearMap F ω₁ f = homogeneousAdelicThetaLinearMap F ω₁ g)
    (hf0 : f (Multiplicative.ofAdd 0) = 0) (hg0 : g (Multiplicative.ofAdd 0) = 0)
    (hgF : adeleSchwartzFourier (F := F) g (Multiplicative.ofAdd 0) = 0) :
    adeleSchwartzFourier (F := F) f (Multiplicative.ofAdd 0) = 0 := by
  subst hω
  dsimp only at hf0 hg0 hgF ⊢
  simp only [ofAdd_zero] at hf0 hg0 hgF ⊢
  obtain ⟨C₁, T₁, hC₁, hT₁, h₁⟩ := homogeneousAdelicTheta_decay_small 1 f 1
  obtain ⟨C₂, T₂, hC₂, hT₂, h₂⟩ := homogeneousAdelicTheta_decay_small 1 g 1
  beta_reduce at h₁ h₂
  set a := adeleSchwartzFourier (F := F) f 1
  set vol := (normOneIdeleClassTamagawaMeasure F univ).toReal
  have hvol : 0 < vol := archNuclearityDenominator_volume_pos F
  have hPf (x : IdeleClassGroup (𝓞 F) F) : homogeneousAdelicTheta_polarTerm 1 f x =
      vol • ((((ideleClassNorm F x : ℝ≥0) : ℝ))⁻¹ • a) := by
    simp [homogeneousAdelicTheta_polarTerm, hf0, vol, a]
  have hPg (x : IdeleClassGroup (𝓞 F) F) : homogeneousAdelicTheta_polarTerm 1 g x = 0 := by
    simp [homogeneousAdelicTheta_polarTerm, hg0, hgF]
  let T := min T₁ T₂
  have key (t : ℝ) (ht : 0 < t) (htT : t < T) : ‖a‖ ≤ (C₁ + C₂) / vol * t ^ 2 := by
    obtain ⟨x, hx⟩ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
      (Units.mk0 (⟨t, ht.le⟩ : ℝ≥0) (fun h ↦ ht.ne' (congrArg Subtype.val h)))
    have hxt : (((ideleClassNorm F x : ℝ≥0) : ℝ)) = t := by rw [hx]; rfl
    have e1 := h₁ x (by rw [hxt]; exact htT.trans_le (min_le_left _ _))
    have e2 := h₂ x (by rw [hxt]; exact htT.trans_le (min_le_right _ _))
    rw [hxt, pow_one] at e1 e2
    rw [hPf, hxt] at e1
    rw [hPg, sub_zero] at e2
    have hθx : homogeneousAdelicTheta 1 f x = homogeneousAdelicTheta 1 g x :=
      DFunLike.congr_fun hθ x
    have hsplit : vol • (t⁻¹ • a) = homogeneousAdelicTheta 1 g x -
        (homogeneousAdelicTheta 1 f x - vol • (t⁻¹ • a)) := by
      rw [hθx]; ring
    have hn : ‖vol • (t⁻¹ • a)‖ ≤ C₁ * t + C₂ * t := by
      rw [hsplit]
      exact (norm_sub_le _ _).trans (by linarith)
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hvol.le,
      Real.norm_of_nonneg (inv_nonneg.mpr ht.le)] at hn
    rw [div_mul_eq_mul_div, le_div_iff₀ hvol]
    have : vol * (t⁻¹ * ‖a‖) * t = ‖a‖ * vol := by field_simp
    nlinarith
  have hT : 0 < T := lt_min hT₁ hT₂
  have hlim : Tendsto (fun t : ℝ ↦ (C₁ + C₂) / vol * t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ ↦ (C₁ + C₂) / vol * t ^ 2) (𝓝 0) (𝓝 ((C₁ + C₂) / vol * 0 ^ 2)) :=
      (continuous_const.mul (continuous_pow 2)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖a‖ ≤ (C₁ + C₂) / vol * t ^ 2 := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht using key t ht.1 ht.2
  exact norm_le_zero_iff.mp (ge_of_tendsto hlim hev)

open MeasureTheory Filter in
/-- A flat test whose theta class is pole-free for the trivial norm-one character has
Fourier value zero at the origin. -/
private theorem archNuclearityDenominator_flat_fourier_eq_zero (F : Type) [Field F] [NumberField F]
    (ω₁ : PontryaginDual (ideleClassNorm F).ker) (hω : ω₁ = 1)
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) (hf : f ∈ globalArchimedeanFlatTests F)
    (hle : (globalArchimedeanFlatTests F).map
      (LinearMap.ker (homogeneousAdelicThetaLinearMap F ω₁)).mkQ ≤
      globalPolarFreeThetaSubmodule ω₁) :
    adeleSchwartzFourier (F := F) f (Multiplicative.ofAdd 0) = 0 := by
  have hm := hle (Submodule.mem_map_of_mem hf)
  obtain ⟨g, hg0, hgF, hgq⟩ := (mem_globalPolarFreeThetaSubmodule ω₁ _).mp hm
  have hθ : homogeneousAdelicThetaLinearMap F ω₁ f = homogeneousAdelicThetaLinearMap F ω₁ g := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.mem_ker,
      map_sub, sub_eq_zero] at hgq
    exact hgq.symm
  exact archNuclearityDenominator_fourier_eq_zero F ω₁ hω f g hθ
    (globalArchimedeanFlatTests_zero_moments f hf).1 hg0 hgF

/-- Paper: Theorem 7.4.3.1(1), p. 368.
Over ℚ with the trivial character, tensor a nonnegative nonzero smooth bump
supported in (2,3) with the indicator of the finite integral adeles. The test is
archimedean-flat and its Fourier value at zero is its strictly positive integral.
That value survives on the trivial homogeneous theta quotient, so no zero-moment
test represents the same class. -/
theorem Printed.archNuclearityDenominator_nonzero_closed_false :
    ¬ Printed.archNuclearityDenominator_nonzero_closed := by
  intro h
  have hle := (h ℚ 1).2.2
  obtain ⟨f, hf, hF⟩ := archNuclearityDenominator_flat_fourier_ne_zero ℚ
  exact hF (archNuclearityDenominator_flat_fourier_eq_zero ℚ _
    (ContinuousMonoidHom.ext fun _ ↦ rfl) f hf hle)

local notation "Θ₀[" F ", " χ "]" => ↥(adelePolarSubspace F) ⧸
  LinearMap.ker ((homogeneousAdelicThetaLinearMap F (ω[F, χ])).domRestrict (adelePolarSubspace F))
local notation "gammaOrder(" χ ", " s ")" =>
  (analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s).toNat
local notation "Z(" χ ", " τ ", " hτ ")" => (exists_globalPolarThetaMellin χ τ hτ).choose
local notation "Aθ(" χ ", " τ ", " hτ ", " φ ")" => (exists_polarThetaNuclearityAction χ τ hτ φ).choose

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The page subtracts one at the quasi-character |·|^(it₀), with χ = |·|^(−it₀)
when the norm-one restriction is trivial. The natural-number difference gives
exactly the allowed derivative orders, including the empty range off the pole set. -/
def Printed.archNuclearityMultiplicity {F : Type*} [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)) (s : ℂ) : ℕ :=
  let x := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  gammaOrder(χ, s) -
    (if ω[F, χ] = 1 ∧ ideleClassNormTwist χ s =
      ideleClassNormTwist (1 : U[F]) (-((x : ℂ) * Complex.I)) then 1 else 0)

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The printed derivative indices use the multiplicity at the character specified on the page. -/
abbrev Printed.ArchNuclearityJetIndex {F : Type*} [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)) :=
  {j : ℂ × ℕ // j.2 < Printed.archNuclearityMultiplicity χ τ hτ j.1}

/-- Paper: Equation (7.4.3.4), p. 368. Evaluate a derivative at a printed jet index. -/
def Printed.archNuclearityJet {F : Type*} [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F))
    (j : Printed.ArchNuclearityJetIndex χ τ hτ) : StrongDual ℂ (Θ₀[F, χ]) :=
  ((entireJet j.val.1 j.val.2).comp schwartzBergmanEntireInclusion).comp (Z(χ, τ, hτ))

section QuotientPredicates

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] {J : Type*}

/-- Paper: Theorem 7.4.3.1(2), p. 368. The strong closure of the derivative
span equals the annihilator of the denominator. -/
def Printed.JetsSpanAnnihilator (D : Submodule ℂ E) (jet : J → StrongDual ℂ E) : Prop :=
  ((Submodule.span ℂ (Set.range jet)).topologicalClosure : Set (StrongDual ℂ E)) =
    {ℓ | ∀ x : D, ℓ x.val = 0}

/-- Paper: Theorem 7.4.3.1(3), p. 368. The specified derivatives descend to a
Schauder basis of the strong quotient dual in each enumeration. -/
def Printed.HasQuotientJetBasis (D : Submodule ℂ E) (jet : J → StrongDual ℂ E) : Prop :=
  ∀ σ : ℕ ≃ J, ∃ (d : ℕ → StrongDual ℂ (E ⧸ D))
    (b : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ D))),
    (∀ n (x : E), d n (D.mkQ x) = jet (σ n) x) ∧ IsSchauderBasis d b

/-- Paper: Equation (7.4.3.14), p. 373. The induced operator has the stated
matrix trace in each enumeration of the specified derivative basis. -/
def Printed.HasQuotientJetTrace (D : Submodule ℂ E) (jet : J → StrongDual ℂ E)
    (A : E →L[ℂ] E) (value : ℂ) : Prop :=
  Printed.HasQuotientJetBasis D jet ∧
    ∃ T : (E ⧸ D) →L[ℂ] (E ⧸ D), (∀ x : E, T (D.mkQ x) = D.mkQ (A x)) ∧
      ∀ (σ : ℕ ≃ J) (d : ℕ → StrongDual ℂ (E ⧸ D))
        (b : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ D))),
        (∀ n (x : E), d n (D.mkQ x) = jet (σ n) x) → IsSchauderBasis d b →
          HasSum (fun n ↦ b n ((d n).comp T)) value

/-- Paper: Remark 7.4.3.3, p. 373. The action descends to a nonnuclear
endomorphism of the quotient. -/
def Printed.HasNonnuclearQuotientAction (D : Submodule ℂ E) (A : E →L[ℂ] E) : Prop :=
  letI : UniformSpace (E ⧸ D) := IsTopologicalAddGroup.rightUniformSpace (E ⧸ D)
  ∃ T : (E ⧸ D) →L[ℂ] (E ⧸ D), (∀ x : E, T (D.mkQ x) = D.mkQ (A x)) ∧
    ¬ Nonempty (NuclearPresentation T)

end QuotientPredicates

/-- Paper: Theorem 7.4.3.1(2), p. 368.
With the multiplicity exception as written on the page, the indicated derivatives
generate the annihilator of the flat image in the strong dual. -/
def Printed.archNuclearityJet_span : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)),
    Printed.JetsSpanAnnihilator (archNuclearityDenominator χ) (Printed.archNuclearityJet χ τ hτ)

/-- The test combination `φ - (3/2) φ(a⁻¹ ·) + (1/2) φ(a⁻² ·)` for the rational idele `a`
of norm two. -/
private def archNuclearityJet_span_false_comb
    (φ : SchwartzBruhat (Multiplicative 𝔸[ℚ])) : SchwartzBruhat (Multiplicative 𝔸[ℚ]) :=
  φ - (3 / 2 : ℂ) • schwartzBruhatUnitTranslate (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero)) φ +
    (1 / 2 : ℂ) • schwartzBruhatUnitTranslate (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero))
      (schwartzBruhatUnitTranslate (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero)) φ)

/-- Away from the two pole characters, the zeta function of the combination is the multiplier
`(1 - 2^w)(1 - 2^w/2)` times that of `φ`. -/
private theorem archNuclearityJet_span_false_mul (φ : SchwartzBruhat (Multiplicative 𝔸[ℚ])) (w : ℂ)
    (h1 : (2 : ℂ) ^ w ≠ 1) (h2 : (2 : ℂ) ^ w ≠ 2) :
    globalIdelicZFunction (archNuclearityJet_span_false_comb φ) (ideleClassNormTwist (1 : U[ℚ]) w) =
      (1 - 3 / 2 * (2 : ℂ) ^ w + 1 / 2 * ((2 : ℂ) ^ w) ^ 2) *
        globalIdelicZFunction φ (ideleClassNormTwist (1 : U[ℚ]) w) := by
  have hval (s : ℂ) : ideleClassNormTwist (1 : U[ℚ]) s (QuotientGroup.mk (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero))) = (2 : ℂ) ^ s := by
    change (((1 : U[ℚ]) (QuotientGroup.mk (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero))) : Circle) : ℂ) *
      (((ideleClassNorm ℚ (QuotientGroup.mk (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero))) : ℝ≥0) : ℝ) : ℂ) ^ s = _
    have hn : ideleClassNorm ℚ (QuotientGroup.mk (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero))) = Units.mk0 (2 : ℝ≥0) two_ne_zero :=
      ratIdeleNormSection_rightInverse _
    rw [hn]
    simp
  have hreg : 0 ≤ globalIdelicOrderBound (ideleClassNormTwist (1 : U[ℚ]) w) := by
    unfold globalIdelicOrderBound
    rw [ite_eq_right]
    rintro (h | h)
    · have := DFunLike.congr_fun h (QuotientGroup.mk (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero)))
      rw [hval] at this
      exact h1 (by simpa using this)
    · have := DFunLike.congr_fun h (QuotientGroup.mk (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero)))
      rw [hval, hval] at this
      exact h2 (by simpa using this)
  let c : {c : QuasiCharacter C[ℚ] // 0 ≤ globalIdelicOrderBound c} := ⟨ideleClassNormTwist (1 : U[ℚ]) w, hreg⟩
  have hT (f : SchwartzBruhat (Multiplicative 𝔸[ℚ])) : globalIdelicZFunction (schwartzBruhatUnitTranslate (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero)) f) (ideleClassNormTwist (1 : U[ℚ]) w) =
      (2 : ℂ) ^ w * globalIdelicZFunction f (ideleClassNormTwist (1 : U[ℚ]) w) := by
    have := globalIdelicMellin_unitTranslate (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero)) f c
    rw [globalIdelicMellin_apply, globalIdelicMellin_apply] at this
    rw [← hval w]
    exact this
  have hlin : globalIdelicZFunction (archNuclearityJet_span_false_comb φ) (ideleClassNormTwist (1 : U[ℚ]) w) =
      globalIdelicZFunction φ (ideleClassNormTwist (1 : U[ℚ]) w) -
        (3 / 2 : ℂ) * globalIdelicZFunction (schwartzBruhatUnitTranslate (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero)) φ) (ideleClassNormTwist (1 : U[ℚ]) w) +
        (1 / 2 : ℂ) * globalIdelicZFunction
          (schwartzBruhatUnitTranslate (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero)) (schwartzBruhatUnitTranslate (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero)) φ)) (ideleClassNormTwist (1 : U[ℚ]) w) := by
    have hmap : globalIdelicMellin (F := ℚ) (archNuclearityJet_span_false_comb φ) = globalIdelicMellin (F := ℚ) φ -
        (3 / 2 : ℂ) • globalIdelicMellin (F := ℚ) (schwartzBruhatUnitTranslate (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero)) φ) +
        (1 / 2 : ℂ) • globalIdelicMellin (F := ℚ)
          (schwartzBruhatUnitTranslate (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero)) (schwartzBruhatUnitTranslate (ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero)) φ)) := by
      simp [archNuclearityJet_span_false_comb, map_add, map_sub, map_smul]
    have := congrArg (fun m ↦ m.val c) hmap
    simp at this
    rw [one_div]
    exact this
  rw [hlin, hT, hT, hT]
  ring


/-- The multiplier `m w = 1 - (3/2) 2^w + (1/2) 4^w` has derivative `-(log 2)/2` at `0`. -/
private theorem archNuclearityJet_span_false_hasDerivAt_mul :
    HasDerivAt (fun w : ℂ ↦ 1 - 3 / 2 * (2 : ℂ) ^ w + 1 / 2 * ((2 : ℂ) ^ w) ^ 2)
      (-(Real.log 2 / 2 : ℂ)) 0 := by
  have hg : HasDerivAt (fun w : ℂ ↦ (2 : ℂ) ^ w) ((2 : ℂ) ^ (0 : ℂ) * Complex.log 2) 0 :=
    (Complex.hasStrictDerivAt_const_cpow (Or.inl two_ne_zero)).hasDerivAt
  have h := ((hg.const_mul (3 / 2 : ℂ)).const_sub 1).add ((hg.pow 2).const_mul (1 / 2 : ℂ))
  convert h using 1
  rw [Complex.cpow_zero, ← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)]
  push_cast
  ring

open Filter in
/-- `2^w ≠ 1` near `0`, off `0`. -/
private theorem archNuclearityJet_span_false_eventually_ne_one :
    ∀ᶠ w in 𝓝[≠] (0 : ℂ), (2 : ℂ) ^ w ≠ 1 := by
  have hg : HasDerivAt (fun w : ℂ ↦ (2 : ℂ) ^ w) ((2 : ℂ) ^ (0 : ℂ) * Complex.log 2) 0 :=
    (Complex.hasStrictDerivAt_const_cpow (Or.inl two_ne_zero)).hasDerivAt
  exact hg.eventually_ne (c := 1) (by
    rw [Complex.cpow_zero, one_mul, ← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)]
    exact Complex.ofReal_ne_zero.mpr (Real.log_pos one_lt_two).ne')

open Filter in
/-- `2^w ≠ 2` near `1`, off `1`. -/
private theorem archNuclearityJet_span_false_eventually_ne_two :
    ∀ᶠ w in 𝓝[≠] (1 : ℂ), (2 : ℂ) ^ w ≠ 2 := by
  have hg : HasDerivAt (fun w : ℂ ↦ (2 : ℂ) ^ w) ((2 : ℂ) ^ (1 : ℂ) * Complex.log 2) 1 :=
    (Complex.hasStrictDerivAt_const_cpow (Or.inl two_ne_zero)).hasDerivAt
  exact hg.eventually_ne (c := 2) (by
    rw [Complex.cpow_one, ← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)]
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (Real.log_pos one_lt_two).ne'))

open Filter in
/-- Residue at `1`: the Fourier value of the combination at zero vanishes. -/
private theorem archNuclearityJet_span_false_fourier (φ : SchwartzBruhat (Multiplicative 𝔸[ℚ])) :
    adeleSchwartzFourier (archNuclearityJet_span_false_comb φ) (Multiplicative.ofAdd 0) = 0 := by
  have hc : Continuous (fun w : ℂ ↦ (2 : ℂ) ^ w) :=
    continuous_iff_continuousAt.2 fun _ ↦ continuousAt_const_cpow two_ne_zero
  have hne1 : ∀ᶠ w in 𝓝[≠] (1 : ℂ), (2 : ℂ) ^ w ≠ 1 := by
    have : ∀ᶠ w in 𝓝 (1 : ℂ), (2 : ℂ) ^ w ≠ 1 :=
      hc.continuousAt.eventually_ne (by rw [Complex.cpow_one]; norm_num)
    exact this.filter_mono nhdsWithin_le_nhds
  have hR := globalIdelicZFunction_residue_one (F := ℚ) (archNuclearityJet_span_false_comb φ)
  have hRφ := globalIdelicZFunction_residue_one (F := ℚ) φ
  have hm : Tendsto (fun w : ℂ ↦ 1 - 3 / 2 * (2 : ℂ) ^ w + 1 / 2 * ((2 : ℂ) ^ w) ^ 2) (𝓝[≠] 1)
      (𝓝 0) := by
    have : Tendsto (fun w : ℂ ↦ 1 - 3 / 2 * (2 : ℂ) ^ w + 1 / 2 * ((2 : ℂ) ^ w) ^ 2) (𝓝 1)
        (𝓝 (1 - 3 / 2 * (2 : ℂ) ^ (1 : ℂ) + 1 / 2 * ((2 : ℂ) ^ (1 : ℂ)) ^ 2)) :=
      ((continuous_const.sub (continuous_const.mul hc)).add
        (continuous_const.mul (hc.pow 2))).tendsto 1
    rw [Complex.cpow_one] at this
    convert this.mono_left nhdsWithin_le_nhds using 2
    norm_num
  have h2 := hm.mul hRφ
  rw [zero_mul] at h2
  have h3 : Tendsto (fun s : ℂ ↦ (s - 1) * globalIdelicZFunction (archNuclearityJet_span_false_comb φ)
      (ideleClassNormTwist (1 : U[ℚ]) s)) (𝓝[≠] 1) (𝓝 0) := by
    refine h2.congr' ?_
    filter_upwards [hne1, archNuclearityJet_span_false_eventually_ne_two] with w hw1 hw2
    rw [archNuclearityJet_span_false_mul φ w hw1 hw2]
    ring
  have hu := tendsto_nhds_unique hR h3
  have hmass := archNuclearityDenominator_volume_pos ℚ
  exact (mul_eq_zero.mp hu).resolve_left (Complex.ofReal_ne_zero.mpr hmass.ne')

open Filter in
/-- Residue at `0`: the combination has a finite limit at the trivial quasi-character. -/
private theorem archNuclearityJet_span_false_tendsto (φ : SchwartzBruhat (Multiplicative 𝔸[ℚ])) :
    Tendsto (fun w : ℂ ↦ globalIdelicZFunction (archNuclearityJet_span_false_comb φ)
        (ideleClassNormTwist (1 : U[ℚ]) w)) (𝓝[≠] 0)
      (𝓝 ((Real.log 2 / 2 : ℂ) * ((normOneIdeleClassTamagawaMeasure ℚ univ).toReal : ℂ) *
        φ (Multiplicative.ofAdd 0))) := by
  have hc : Continuous (fun w : ℂ ↦ (2 : ℂ) ^ w) :=
    continuous_iff_continuousAt.2 fun _ ↦ continuousAt_const_cpow two_ne_zero
  have hne2 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), (2 : ℂ) ^ w ≠ 2 := by
    have : ∀ᶠ w in 𝓝 (0 : ℂ), (2 : ℂ) ^ w ≠ 2 :=
      hc.continuousAt.eventually_ne (by rw [Complex.cpow_zero]; norm_num)
    exact this.filter_mono nhdsWithin_le_nhds
  have hslope := hasDerivAt_iff_tendsto_slope.mp archNuclearityJet_span_false_hasDerivAt_mul
  have hRφ := globalIdelicZFunction_residue_zero (F := ℚ) φ
  have h2 := hslope.mul hRφ
  have h3 : Tendsto (fun w : ℂ ↦ globalIdelicZFunction (archNuclearityJet_span_false_comb φ)
      (ideleClassNormTwist (1 : U[ℚ]) w)) (𝓝[≠] 0)
      (𝓝 (-(Real.log 2 / 2 : ℂ) * (-((normOneIdeleClassTamagawaMeasure ℚ univ).toReal : ℂ) *
        φ (Multiplicative.ofAdd 0)))) := by
    refine h2.congr' ?_
    filter_upwards [archNuclearityJet_span_false_eventually_ne_one, hne2, self_mem_nhdsWithin]
      with w hw1 hw2 hw0
    rw [archNuclearityJet_span_false_mul φ w hw1 hw2, slope_def_field]
    simp only [Complex.cpow_zero, sub_zero]
    have hw0' : w ≠ 0 := hw0
    field_simp
    ring
  convert h3 using 2
  ring

/-- The rational section acts on the real coordinate by multiplication. -/
private theorem archNuclearityJet_span_false_section_fst (t : ℝ≥0ˣ) (x : InfiniteAdeleRing ℚ) :
    InfiniteAdeleRing.ringEquiv_mixedSpace ℚ ((ratIdeleNormSection t : 𝔸[ℚ]).1 * x) =
      ((t : ℝ≥0) : ℝ) • InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x := by
  have hc (v : {v : InfinitePlace ℚ // v.IsComplex}) : False :=
    InfinitePlace.not_isComplex_iff_isReal.mpr
      ((Subsingleton.elim v.val Rat.infinitePlace) ▸ Rat.isReal_infinitePlace) v.property
  refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ (hc v).elim)
  obtain ⟨v, hv⟩ := v
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  change InfinitePlace.Completion.ringEquivRealOfIsReal hv
      ((ratIdeleNormSection t : 𝔸[ℚ]).1 Rat.infinitePlace * x Rat.infinitePlace) =
    ((t : ℝ≥0) : ℝ) * InfinitePlace.Completion.ringEquivRealOfIsReal hv (x Rat.infinitePlace)
  rw [map_mul]
  congr 1
  change InfinitePlace.Completion.ringEquivRealOfIsReal hv
      (MonoidHom.mulSingle InfinitePlace.Completion Rat.infinitePlace
        ((InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm
          ((t : ℝ≥0) : ℝ)) Rat.infinitePlace) = _
  rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
  exact RingEquiv.apply_symm_apply _ _

/-- Translating by `a₂` halves the real coordinate and fixes the finite part. -/
private theorem archNuclearityJet_span_false_translate (x : 𝔸[ℚ]) :
    InfiniteAdeleRing.ringEquiv_mixedSpace ℚ
        (((ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero))⁻¹ : (IdeleGroup (𝓞 ℚ) ℚ)) * x).1 =
      (1 / 2 : ℝ) • InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1 ∧
    (((ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero))⁻¹ : (IdeleGroup (𝓞 ℚ) ℚ)) * x).2 =
      x.2 := by
  rw [← map_inv]
  refine ⟨?_, ?_⟩
  · rw [Prod.fst_mul, archNuclearityJet_span_false_section_fst]
    congr 1
    simp
  · rw [Prod.snd_mul]
    exact one_mul _

open scoped TensorProduct in
/-- For any finite factor `g` with `g 0 = 1`, the tensor of a bump equal to one near zero with `g`
gives a combination that is a flat zero-moment tensor. -/
private theorem archNuclearityJet_span_false_test_of
    (g : SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 ℚ) ℚ)))
    (hg : g (Multiplicative.ofAdd 0) = 1) :
    ∃ φ : SchwartzBruhat (Multiplicative 𝔸[ℚ]), φ (Multiplicative.ofAdd 0) = 1 ∧
      archNuclearityJet_span_false_comb φ ∈ globalArchimedeanFlatTests ℚ True := by
  let Coord := ({v : InfinitePlace ℚ // v.IsReal} → ℝ) × ({v : InfinitePlace ℚ // v.IsComplex} → ℂ)
  have hc (v : {v : InfinitePlace ℚ // v.IsComplex}) : False :=
    InfinitePlace.not_isComplex_iff_isReal.mpr
      ((Subsingleton.elim v.val Rat.infinitePlace) ▸ Rat.isReal_infinitePlace) v.property
  let b : ContDiffBump (0 : Coord) := ⟨1, 2, one_pos, one_lt_two⟩
  let F0 : Coord → ℂ := fun u ↦ ((b u : ℝ) : ℂ)
  have hF0 : ContDiff ℝ (⊤ : ℕ∞) F0 := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hF0s : HasCompactSupport F0 := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hF01 (u : Coord) (hu : ‖u‖ ≤ 1) : F0 u = 1 := by
    have : b u = 1 := b.one_of_mem_closedBall (by simpa using hu)
    simp [F0, this]
  have h2 : HasCompactSupport fun u : Coord ↦ F0 ((1 / 2 : ℝ) • u) :=
    hF0s.comp_smul (by norm_num)
  have h4 : HasCompactSupport fun u : Coord ↦ F0 ((1 / 4 : ℝ) • u) :=
    hF0s.comp_smul (by norm_num)
  let H : Coord → ℂ := fun u ↦ F0 u - (3 / 2 : ℂ) * F0 ((1 / 2 : ℝ) • u) +
    (1 / 2 : ℂ) * F0 ((1 / 4 : ℝ) • u)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    (hF0.sub (contDiff_const.mul (hF0.comp (contDiff_const_smul _)))).add
      (contDiff_const.mul (hF0.comp (contDiff_const_smul _)))
  have hHs : HasCompactSupport H := (hF0s.sub h2.mul_left).add h4.mul_left
  have hH0 (u : Coord) (hu : ‖u‖ < 1) : H u = 0 := by
    have h1 : ‖(1 / 2 : ℝ) • u‖ ≤ 1 := by
      rw [norm_smul]; norm_num; linarith [norm_nonneg u]
    have h2 : ‖(1 / 4 : ℝ) • u‖ ≤ 1 := by
      rw [norm_smul]; norm_num; linarith [norm_nonneg u]
    simp only [H, hF01 u hu.le, hF01 _ h1, hF01 _ h2]
    norm_num
  let hS : SchwartzMap Coord ℂ := hHs.toSchwartzMap hH
  let h0 : SchwartzMap Coord ℂ := hF0s.toSchwartzMap hF0
  have hhS (u : Coord) : hS u = H u := rfl
  have hh0 (u : Coord) : h0 u = F0 u := rfl
  have hflat : hS ∈ archimedeanFlatSchwartz (ι := {v : InfinitePlace ℚ // v.IsReal})
      (κ := {v : InfinitePlace ℚ // v.IsComplex}) := by
    apply mem_archimedeanFlatSchwartz_of_tsupport
    rw [Set.disjoint_left]
    intro u hu hw
    have hu0 : u = 0 := by
      rcases hw with ⟨i, hi⟩ | ⟨j, -⟩
      · refine Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ (hc k).elim)
        rw [Subsingleton.elim k i]; exact hi
      · exact (hc j).elim
    subst hu0
    refine notMem_tsupport_iff_eventuallyEq.mpr ?_ hu
    filter_upwards [Metric.ball_mem_nhds (0 : Coord) one_pos] with u hu
    exact hH0 u (by simpa using hu)
  have hd : Module.finrank ℝ Coord = 1 := by
    have : Subsingleton ({v : InfinitePlace ℚ // v.IsComplex} → ℂ) :=
      ⟨fun f g ↦ funext fun k ↦ (hc k).elim⟩
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_zero_of_subsingleton, add_zero]
    exact Fintype.card_eq_one_iff.mpr ⟨⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩,
      fun v ↦ Subtype.ext (Subsingleton.elim _ _)⟩
  have hmom : (∫ u : Coord, hS u) = 0 := by
    have hi0 : MeasureTheory.Integrable F0 :=
      hF0.continuous.integrable_of_hasCompactSupport hF0s
    have hi2 : MeasureTheory.Integrable fun u : Coord ↦ F0 ((1 / 2 : ℝ) • u) :=
      (hF0.continuous.comp (continuous_const_smul _)).integrable_of_hasCompactSupport h2
    have hi4 : MeasureTheory.Integrable fun u : Coord ↦ F0 ((1 / 4 : ℝ) • u) :=
      (hF0.continuous.comp (continuous_const_smul _)).integrable_of_hasCompactSupport h4
    simp only [hhS, H]
    rw [MeasureTheory.integral_add (f := fun u ↦ F0 u - 3 / 2 * F0 ((1 / 2 : ℝ) • u))
        (g := fun u ↦ 1 / 2 * F0 ((1 / 4 : ℝ) • u)) (hi0.sub (hi2.const_mul _)) (hi4.const_mul _),
      MeasureTheory.integral_sub (f := F0) (g := fun u ↦ 3 / 2 * F0 ((1 / 2 : ℝ) • u))
        hi0 (hi2.const_mul _), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, MeasureTheory.Measure.integral_comp_smul,
      MeasureTheory.Measure.integral_comp_smul, hd, Complex.real_smul, Complex.real_smul]
    norm_num
    ring
  have hinf (h : SchwartzMap Coord ℂ) := (mem_archimedeanSchwartzBruhat_iff (F := ℚ)
    (fun x ↦ h (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x))).mpr ⟨h, fun _ ↦ rfl⟩
  let fI (h : SchwartzMap Coord ℂ) : SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)) :=
    ⟨_, hinf h⟩
  let tensor := (adeleSchwartz_inductiveTensor_equiv ℚ).choose
  have hval (h : SchwartzMap Coord ℂ) (x : 𝔸[ℚ]) : tensor (fI h ⊗ₜ[ℂ] g) (Multiplicative.ofAdd x) =
      h (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1) * g (Multiplicative.ofAdd x.2) :=
    (adeleSchwartz_inductiveTensor_equiv ℚ).choose_spec (fI h) g x
  refine ⟨tensor (fI h0 ⊗ₜ[ℂ] g), ?_, ?_⟩
  · rw [hval, hh0, Prod.fst_zero, Prod.snd_zero, map_zero, hF01 0 (by rw [norm_zero]; exact zero_le_one),
      one_mul]
    exact hg
  · have heq : archNuclearityJet_span_false_comb (tensor (fI h0 ⊗ₜ[ℂ] g)) =
        tensor (fI hS ⊗ₜ[ℂ] g) := by
      refine SchwartzBruhat.ext fun y ↦ ?_
      obtain ⟨x, rfl⟩ : ∃ x, Multiplicative.ofAdd x = y := ⟨Multiplicative.toAdd y, rfl⟩
      let a := ratIdeleNormSection (Units.mk0 (2 : ℝ≥0) two_ne_zero)
      have e1 := archNuclearityJet_span_false_translate x
      have e2 := archNuclearityJet_span_false_translate (((a⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : 𝔸[ℚ]) * x)
      change tensor (fI h0 ⊗ₜ[ℂ] g) (Multiplicative.ofAdd x) -
          (3 / 2 : ℂ) * tensor (fI h0 ⊗ₜ[ℂ] g)
            (Multiplicative.ofAdd (((a⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : 𝔸[ℚ]) * x)) +
          (1 / 2 : ℂ) * tensor (fI h0 ⊗ₜ[ℂ] g)
            (Multiplicative.ofAdd (((a⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : 𝔸[ℚ]) *
              (((a⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : 𝔸[ℚ]) * x))) =
        tensor (fI hS ⊗ₜ[ℂ] g) (Multiplicative.ofAdd x)
      rw [hval, hval, hval, hval, e2.1, e2.2, e1.1, e1.2, hh0, hh0, hh0, hhS, smul_smul,
        show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
      simp only [H]
      ring
    rw [heq]
    exact Submodule.subset_span ⟨fI hS, g, ⟨hS, hflat⟩, fun _ ↦ rfl, fun _ ↦ hmom, rfl⟩

open scoped TensorProduct in
/-- A bump equal to one near zero, tensored with the indicator of the integral finite adeles. -/
private theorem archNuclearityJet_span_false_test :
    ∃ φ : SchwartzBruhat (Multiplicative 𝔸[ℚ]), φ (Multiplicative.ofAdd 0) = 1 ∧
      archNuclearityJet_span_false_comb φ ∈ globalArchimedeanFlatTests ℚ True :=
  archNuclearityJet_span_false_test_of ⟨_, archNuclearityDenominator_finiteIndicator_mem ℚ⟩
    (ite_eq_left_iff.mpr fun h ↦ (h (archNuclearityDenominator_integralSubgroup ℚ).one_mem).elim)

open Filter in
/-- A flat zero-moment polar test whose zeta function at the trivial quasi-character is
nonzero. -/
private theorem archNuclearityJet_span_false_key :
    ∃ f : adelePolarSubspace ℚ, f.val ∈ globalArchimedeanFlatTests ℚ True ∧
      globalIdelicZFunction f.val (ideleClassNormTwist (1 : U[ℚ]) 0) ≠ 0 := by
  obtain ⟨φ, hφ0, hflat⟩ := archNuclearityJet_span_false_test
  have hpolar : archNuclearityJet_span_false_comb φ ∈ adelePolarSubspace ℚ :=
    ((globalArchimedeanFlatTests_zero_moments (archNuclearityJet_span_false_comb φ)
      (Submodule.span_mono (by rintro _ ⟨f, g, h, h1, -, h3⟩; exact ⟨f, g, h, h1, fun h ↦ h.elim, h3⟩) hflat)).2).mpr
      (archNuclearityJet_span_false_fourier φ)
  refine ⟨⟨archNuclearityJet_span_false_comb φ, hpolar⟩, hflat, ?_⟩
  let τ : ℝ≥0ˣ →ₜ* I[ℚ] := ⟨ratIdeleNormSection, ratIdeleNormSection_continuous⟩
  have hτ : RightInverse τ (ideleNorm ℚ) := ratIdeleNormSection_rightInverse
  have hspec := (exists_globalPolarThetaMellin (1 : U[ℚ]) τ hτ).choose_spec ⟨archNuclearityJet_span_false_comb φ, hpolar⟩
  let v := (Z((1 : U[ℚ]), τ, hτ)) (Submodule.Quotient.mk ⟨archNuclearityJet_span_false_comb φ, hpolar⟩)
  have hcont : Continuous (fun w : ℂ ↦ globalIdelicZFunction (archNuclearityJet_span_false_comb φ) (ideleClassNormTwist (1 : U[ℚ]) w)) := by
    have : (fun w : ℂ ↦ globalIdelicZFunction (archNuclearityJet_span_false_comb φ) (ideleClassNormTwist (1 : U[ℚ]) w)) =
        fun w ↦ (schwartzBergmanEntireInclusion v).val w :=
      funext fun w ↦ ((hspec w).2).symm.trans (schwartzBergmanEntireInclusion_apply v w).symm
    rw [this]
    exact (schwartzBergmanEntireInclusion v).val.continuous
  have hlim := tendsto_nhds_unique
    ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds) (archNuclearityJet_span_false_tendsto φ)
  rw [hlim, hφ0, mul_one]
  have hm := archNuclearityDenominator_volume_pos ℚ
  have hl : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  refine mul_ne_zero (div_ne_zero ?_ two_ne_zero) (Complex.ofReal_ne_zero.mpr hm.ne')
  exact_mod_cast hl.ne'

/-- The unitary character `|·|^i` of the rational idele class group. -/
private theorem archNuclearityJet_span_false_char :
    ∃ χ : U[ℚ], ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[ℚ]) Complex.I := by
  let c := ideleClassNormTwist (1 : U[ℚ]) Complex.I
  have hn (g : C[ℚ]) : ‖c g‖ = 1 := by
    change ‖(1 : ℂ) * (((ideleClassNorm ℚ g : ℝ≥0) : ℝ) : ℂ) ^ Complex.I‖ = 1
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp
  let χ : U[ℚ] :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hn g)⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun a b ↦ Subtype.ext (map_mul c a b)
      continuous_toFun := c.continuous.subtype_mk _ }
  refine ⟨χ, ?_⟩
  ext1 g
  change c g * _ ^ (0 : ℂ) = c g
  simp

/-- The value of `χ` on an idele class, for `χ = |·|^i`. -/
private theorem archNuclearityJet_span_false_char_apply (χ : U[ℚ])
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[ℚ]) Complex.I) (g : C[ℚ]) :
    (χ g : ℂ) = (((ideleClassNorm ℚ g : ℝ≥0) : ℝ) : ℂ) ^ Complex.I := by
  have h := DFunLike.congr_fun hχ g
  change (χ g : ℂ) * (((ideleClassNorm ℚ g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) =
    (1 : ℂ) * (((ideleClassNorm ℚ g : ℝ≥0) : ℝ) : ℂ) ^ Complex.I at h
  rwa [Complex.cpow_zero, mul_one, one_mul] at h

/-- `|·|^i` is trivial on norm-one classes. -/
private theorem archNuclearityJet_span_false_omega (χ : U[ℚ])
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[ℚ]) Complex.I) :
    ω[ℚ, χ] = 1 := by
  ext1 g
  apply Circle.ext
  change (χ g.val : ℂ) = 1
  rw [archNuclearityJet_span_false_char_apply χ hχ, MonoidHom.mem_ker.mp g.property]
  simp

/-- The archimedean parameters of `|·|^i` are `(i, 0)`. -/
private theorem archNuclearityJet_span_false_params (χ : U[ℚ])
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[ℚ]) Complex.I)
    (v : InfinitePlace ℚ) (hv : v.IsReal) :
    (realHeckeCharacter_parameters χ v hv).exists.choose = (Complex.I, 0) := by
  apply (realHeckeCharacter_parameters χ v hv).unique
    (realHeckeCharacter_parameters χ v hv).exists.choose_spec
  refine ⟨Complex.I_re, fun x ↦ ?_⟩
  rw [hχ]
  let u := Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom x
  change (1 : ℂ) * (((ideleClassNorm ℚ (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ v u) : ℝ≥0) : ℝ) : ℂ) ^
      Complex.I = (‖(x : ℝ)‖ : ℂ) ^ Complex.I * _ ^ ((0 : Fin 2).val)
  rw [ideleClassNorm_ofCompletion, hv.mult_eq_one, pow_one]
  have hn : ((↑(Units.map nnNormHom.toMonoidHom u) : ℝ≥0) : ℝ) = ‖(x : ℝ)‖ := by
    let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
    change ‖e (x : ℝ)‖ = ‖(x : ℝ)‖
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.isometry.norm_map_of_map_zero
      (map_zero e) (x : ℝ)
  rw [hn, one_mul, Fin.val_zero, pow_zero, mul_one]

/-- The gamma factor of `|·|^i` vanishes at `-i`. -/
private theorem archNuclearityJet_span_false_gamma_zero (χ : U[ℚ])
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[ℚ]) Complex.I) :
    heckeGammaFactor χ (-Complex.I) = 0 := by
  unfold heckeGammaFactor
  apply Finset.prod_eq_zero (Finset.mem_univ Rat.infinitePlace)
  rw [dite_eq_left_of_eq_true (eq_true Rat.isReal_infinitePlace)]
  dsimp only
  rw [archNuclearityJet_span_false_params χ hχ]
  simp [Complex.Gammaℝ]

/-- The reciprocal gamma factor of `|·|^i` has positive finite order at `-i`. -/
private theorem archNuclearityJet_span_false_gammaOrder_pos (χ : U[ℚ])
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[ℚ]) Complex.I) :
    0 < (analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) (-Complex.I)).toNat := by
  have han : AnalyticOnNhd ℂ (fun z ↦ (heckeGammaFactor χ z)⁻¹) univ :=
    fun z _ ↦ (differentiable_inv_heckeGammaFactor χ).analyticAt z
  have h0 : analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) (-Complex.I) ≠ 0 := by
    rw [Ne, (han _ trivial).analyticOrderAt_eq_zero, archNuclearityJet_span_false_gamma_zero χ hχ]
    simp
  have h1 : analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) 1 ≠ ⊤ := by
    rw [(han _ trivial).analyticOrderAt_eq_zero.mpr
      (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (by simp)))]
    exact ENat.zero_ne_top
  have htop := han.analyticOrderAt_ne_top_of_isPreconnected (y := -Complex.I) isPreconnected_univ trivial trivial h1
  generalize analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) (-Complex.I) = n at h0 htop ⊢
  induction n using ENat.recTopCoe with
  | top => exact absurd rfl htop
  | coe n => simpa [Nat.pos_iff_ne_zero] using h0

/-- `(e^π)^(-i) = -1`. -/
private theorem archNuclearityJet_span_false_exp_pi :
    ((Real.exp Real.pi : ℝ) : ℂ) ^ (-Complex.I) = -1 := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, mul_neg, Complex.exp_neg,
    Complex.exp_pi_mul_I]
  norm_num

/-- `(e^π)^i = -1`. -/
private theorem archNuclearityJet_span_false_exp_pi' :
    ((Real.exp Real.pi : ℝ) : ℂ) ^ Complex.I = -1 := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.exp_pi_mul_I]

/-- The printed index contains `(-i, 0)` for `|·|^i`. -/
private theorem archNuclearityJet_span_false_mult (χ : U[ℚ])
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[ℚ]) Complex.I)
    (τ : ℝ≥0ˣ →ₜ* I[ℚ]) (hτ : RightInverse τ (ideleNorm ℚ)) :
    0 < Printed.archNuclearityMultiplicity χ τ hτ (-Complex.I) := by
  have hph := existsUnique_ideleNormSection_character_phase χ τ hτ
  have hnorm (t : ℝ≥0ˣ) : ideleClassNorm ℚ (QuotientGroup.mk (τ t)) = t := hτ t
  have h1 : ∀ t : ℝ≥0ˣ, (χ (QuotientGroup.mk (τ t)) : ℂ) =
      (((t : ℝ≥0) : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [archNuclearityJet_span_false_char_apply χ hχ, hnorm, Complex.ofReal_one, one_mul]
  have hx1 : hph.exists.choose = 1 := hph.unique hph.exists.choose_spec h1
  have hif : ¬ (ω[ℚ, χ] = 1 ∧ ideleClassNormTwist χ (-Complex.I) =
      ideleClassNormTwist (1 : U[ℚ]) (-((hph.exists.choose : ℂ) * Complex.I))) := by
    rintro ⟨-, h⟩
    rw [hx1, Complex.ofReal_one, one_mul] at h
    let t : ℝ≥0ˣ := Units.mk0 ⟨Real.exp Real.pi, (Real.exp_pos _).le⟩
      (fun h ↦ (Real.exp_pos Real.pi).ne' (congrArg Subtype.val h))
    have he := DFunLike.congr_fun h (QuotientGroup.mk (τ t))
    change (χ (QuotientGroup.mk (τ t)) : ℂ) *
        (((ideleClassNorm ℚ (QuotientGroup.mk (τ t)) : ℝ≥0) : ℝ) : ℂ) ^ (-Complex.I) =
      (1 : ℂ) * (((ideleClassNorm ℚ (QuotientGroup.mk (τ t)) : ℝ≥0) : ℝ) : ℂ) ^ (-Complex.I) at he
    rw [archNuclearityJet_span_false_char_apply χ hχ, hnorm] at he
    have ht : (((t : ℝ≥0) : ℝ) : ℂ) = ((Real.exp Real.pi : ℝ) : ℂ) := rfl
    rw [ht, archNuclearityJet_span_false_exp_pi, archNuclearityJet_span_false_exp_pi'] at he
    norm_num at he
  unfold Printed.archNuclearityMultiplicity
  dsimp only
  rw [ite_eq_right_iff.mpr fun h ↦ absurd h hif, Nat.sub_zero]
  exact archNuclearityJet_span_false_gammaOrder_pos χ hχ

/-- Paper: Theorem 7.4.3.1(2), p. 368.
For χ = |·|^i over ℚ the printed index includes evaluation at s = −i. Let h be
a nonzero nonnegative bump in (2,3). The real test h(x) − 2 h(2x) is flat with
integral zero. With finite integer indicators its zeta value at the trivial
quasi-character is proportional to (1 − 2) ζ(0) times the nonzero Mellin moment
of h at zero. This jet is nonzero on the flat denominator. -/
theorem Printed.archNuclearityJet_span_false : ¬ Printed.archNuclearityJet_span := by
  intro h
  obtain ⟨χ, hχ⟩ := archNuclearityJet_span_false_char
  let τ : ℝ≥0ˣ →ₜ* I[ℚ] := ⟨ratIdeleNormSection, ratIdeleNormSection_continuous⟩
  have hτ : RightInverse τ (ideleNorm ℚ) := ratIdeleNormSection_rightInverse
  have hspan := h ℚ χ τ hτ
  have hω := archNuclearityJet_span_false_omega χ hχ
  obtain ⟨f, hfD, hne⟩ := archNuclearityJet_span_false_key
  let j : Printed.ArchNuclearityJetIndex χ τ hτ := ⟨(-Complex.I, 0), archNuclearityJet_span_false_mult χ hχ τ hτ⟩
  have hmem : Printed.archNuclearityJet χ τ hτ j ∈
      {ℓ : StrongDual ℂ (Θ₀[ℚ, χ]) | ∀ x : archNuclearityDenominator χ, ℓ x.val = 0} := by
    rw [← hspan]
    exact subset_closure (Submodule.subset_span ⟨j, rfl⟩)
  have hD : (Submodule.Quotient.mk f : Θ₀[ℚ, χ]) ∈ archNuclearityDenominator χ :=
    Submodule.subset_span ⟨f, by rw [eq_true hω]; exact hfD, rfl⟩
  have hz := hmem ⟨_, hD⟩
  apply hne
  have htw : ideleClassNormTwist χ (-Complex.I) = ideleClassNormTwist (1 : U[ℚ]) 0 := by
    have := ideleClassNormTwist_add_of_eq hχ (-Complex.I)
    simpa using this
  rw [← htw, ← ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f (-Complex.I)).2]
  unfold Printed.archNuclearityJet at hz
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply,
    iteratedDeriv_zero, schwartzBergmanEntireInclusion_apply] at hz
  exact hz

/-- Paper: Theorem 7.4.3.1(3), p. 368.
Every enumeration of the printed derivatives gives a basis of the strong quotient dual. -/
def Printed.archNuclearityJet_basis : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)),
    Printed.HasQuotientJetBasis (archNuclearityDenominator χ) (Printed.archNuclearityJet χ τ hτ)

/-- The gamma factor of `|·|^i` vanishes at every point `-i - 2n` of the real pole
progression. -/
private theorem archNuclearityJet_basis_false_gamma_zero (χ : U[ℚ])
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[ℚ]) Complex.I) (n : ℕ) :
    heckeGammaFactor χ (-Complex.I - 2 * (n : ℂ)) = 0 := by
  unfold heckeGammaFactor
  apply Finset.prod_eq_zero (Finset.mem_univ Rat.infinitePlace)
  rw [dite_eq_left_of_eq_true (eq_true Rat.isReal_infinitePlace)]
  dsimp only
  rw [archNuclearityJet_span_false_params χ hχ]
  rw [Complex.Gammaℝ_eq_zero_iff]
  refine ⟨n, ?_⟩
  simp only [Fin.val_zero, Nat.cast_zero, add_zero]
  ring

/-- The reciprocal gamma factor of `|·|^i` has positive finite order at each `-i - 2n`. -/
private theorem archNuclearityJet_basis_false_gammaOrder_pos (χ : U[ℚ])
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[ℚ]) Complex.I) (n : ℕ) :
    0 < (analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) (-Complex.I - 2 * (n : ℂ))).toNat := by
  have han : AnalyticOnNhd ℂ (fun z ↦ (heckeGammaFactor χ z)⁻¹) univ :=
    fun z _ ↦ (differentiable_inv_heckeGammaFactor χ).analyticAt z
  have h0 : analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) (-Complex.I - 2 * (n : ℂ)) ≠ 0 := by
    rw [Ne, (han _ trivial).analyticOrderAt_eq_zero,
      archNuclearityJet_basis_false_gamma_zero χ hχ n]
    simp
  have h1 : analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) 1 ≠ ⊤ := by
    rw [(han _ trivial).analyticOrderAt_eq_zero.mpr
      (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (by simp)))]
    exact ENat.zero_ne_top
  have htop := han.analyticOrderAt_ne_top_of_isPreconnected (y := -Complex.I - 2 * (n : ℂ))
    isPreconnected_univ trivial trivial h1
  generalize analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) (-Complex.I - 2 * (n : ℂ)) = m
    at h0 htop ⊢
  induction m using ENat.recTopCoe with
  | top => exact absurd rfl htop
  | coe m => simpa [Nat.pos_iff_ne_zero] using h0

/-- The printed index contains `(-i - 2n, 0)` for every `n`: the norm-character correction
never fires on the real pole progression. -/
private theorem archNuclearityJet_basis_false_mult (χ : U[ℚ])
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[ℚ]) Complex.I)
    (τ : ℝ≥0ˣ →ₜ* I[ℚ]) (hτ : RightInverse τ (ideleNorm ℚ)) (n : ℕ) :
    0 < Printed.archNuclearityMultiplicity χ τ hτ (-Complex.I - 2 * (n : ℂ)) := by
  have hph := existsUnique_ideleNormSection_character_phase χ τ hτ
  have hnorm (t : ℝ≥0ˣ) : ideleClassNorm ℚ (QuotientGroup.mk (τ t)) = t := hτ t
  have h1 : ∀ t : ℝ≥0ˣ, (χ (QuotientGroup.mk (τ t)) : ℂ) =
      (((t : ℝ≥0) : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [archNuclearityJet_span_false_char_apply χ hχ, hnorm, Complex.ofReal_one, one_mul]
  have hx1 : hph.exists.choose = 1 := hph.unique hph.exists.choose_spec h1
  have hif : ¬ (ω[ℚ, χ] = 1 ∧ ideleClassNormTwist χ (-Complex.I - 2 * (n : ℂ)) =
      ideleClassNormTwist (1 : U[ℚ]) (-((hph.exists.choose : ℂ) * Complex.I))) := by
    rintro ⟨-, h⟩
    rw [hx1, Complex.ofReal_one, one_mul] at h
    let t : ℝ≥0ˣ := Units.mk0 ⟨Real.exp Real.pi, (Real.exp_pos _).le⟩
      (fun h ↦ (Real.exp_pos Real.pi).ne' (congrArg Subtype.val h))
    have he := DFunLike.congr_fun h (QuotientGroup.mk (τ t))
    change (χ (QuotientGroup.mk (τ t)) : ℂ) *
        (((ideleClassNorm ℚ (QuotientGroup.mk (τ t)) : ℝ≥0) : ℝ) : ℂ) ^
          (-Complex.I - 2 * (n : ℂ)) =
      (1 : ℂ) * (((ideleClassNorm ℚ (QuotientGroup.mk (τ t)) : ℝ≥0) : ℝ) : ℂ) ^
          (-Complex.I) at he
    rw [archNuclearityJet_span_false_char_apply χ hχ, hnorm] at he
    have ht : (((t : ℝ≥0) : ℝ) : ℂ) = ((Real.exp Real.pi : ℝ) : ℂ) := rfl
    rw [ht] at he
    have hL : ((Real.exp Real.pi : ℝ) : ℂ) ^ Complex.I *
        ((Real.exp Real.pi : ℝ) : ℂ) ^ (-Complex.I - 2 * (n : ℂ)) =
        ((Real.exp (-(2 * (n : ℝ) * Real.pi)) : ℝ) : ℂ) := by
      rw [← Complex.cpow_add Complex.I (-Complex.I - 2 * (n : ℂ))
        (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]
      rw [show Complex.I + (-Complex.I - 2 * (n : ℂ)) = -2 * (n : ℂ) by ring]
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
        ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
      rw [show (Real.pi : ℂ) * (-2 * (n : ℂ)) =
        ((-(2 * (n : ℝ) * Real.pi) : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.ofReal_exp]
    rw [hL, one_mul, archNuclearityJet_span_false_exp_pi] at he
    have hre := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.one_re] at hre
    have := Real.exp_pos (-(2 * (n : ℝ) * Real.pi))
    linarith
  unfold Printed.archNuclearityMultiplicity
  dsimp only
  rw [ite_eq_right_iff.mpr fun h ↦ absurd h hif, Nat.sub_zero]
  exact archNuclearityJet_basis_false_gammaOrder_pos χ hχ n

/-- The printed jet index set for `|·|^i` over `ℚ` is countably infinite: it lies over the
discrete gamma-pole set and contains `(-i - 2n, 0)` for every `n`. -/
private theorem archNuclearityJet_basis_false_index_equiv (χ : U[ℚ])
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[ℚ]) Complex.I)
    (τ : ℝ≥0ˣ →ₜ* I[ℚ]) (hτ : RightInverse τ (ideleNorm ℚ)) :
    Nonempty (ℕ ≃ Printed.ArchNuclearityJetIndex χ τ hτ) := by
  let S := {s : ℂ | 0 < (analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s).toNat}
  have hS : S.Countable := by
    have hd := (archNuclearityPoleSet_discrete χ).2
    have : DiscreteTopology S := hd.to_subtype
    exact Set.countable_coe_iff.mp
      (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)
  have hmem (j : Printed.ArchNuclearityJetIndex χ τ hτ) : j.val.1 ∈ S := by
    have h := j.property
    unfold Printed.archNuclearityMultiplicity at h
    dsimp only at h
    show 0 < (analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) j.val.1).toNat
    omega
  have : Countable (Printed.ArchNuclearityJetIndex χ τ hτ) := by
    have := hS.to_subtype
    refine Function.Injective.countable
      (f := fun j : Printed.ArchNuclearityJetIndex χ τ hτ ↦ ((⟨j.val.1, hmem j⟩ : S), j.val.2)) ?_
    intro a b h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  have : Infinite (Printed.ArchNuclearityJetIndex χ τ hτ) := by
    refine Infinite.of_injective
      (fun n : ℕ ↦ (⟨(-Complex.I - 2 * (n : ℂ), 0),
        archNuclearityJet_basis_false_mult χ hχ τ hτ n⟩ :
          Printed.ArchNuclearityJetIndex χ τ hτ)) ?_
    intro a b h
    have h1 : (-Complex.I - 2 * (a : ℂ)) = -Complex.I - 2 * (b : ℂ) :=
      congrArg (fun j : Printed.ArchNuclearityJetIndex χ τ hτ ↦ j.val.1) h
    have h2 := congrArg Complex.re h1
    simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, Complex.I_re] at h2
    norm_num at h2
    exact_mod_cast h2
  exact ⟨(nonempty_equiv_of_countable (α := Printed.ArchNuclearityJetIndex χ τ hτ)).some.symm⟩

/-- Paper: Theorem 7.4.3.1(3), p. 368.
The same flat test h(x) − 2 h(2x) has nonzero evaluation at the printed index
(−i, 0) for the rational character |·|^i. A functional on the quotient vanishes
on the class of this test. -/
theorem Printed.archNuclearityJet_basis_false : ¬ Printed.archNuclearityJet_basis := by
  intro h
  obtain ⟨χ, hχ⟩ := archNuclearityJet_span_false_char
  let τ : ℝ≥0ˣ →ₜ* I[ℚ] := ⟨ratIdeleNormSection, ratIdeleNormSection_continuous⟩
  have hτ : RightInverse τ (ideleNorm ℚ) := ratIdeleNormSection_rightInverse
  obtain ⟨σ⟩ := archNuclearityJet_basis_false_index_equiv χ hχ τ hτ
  obtain ⟨d, -, hd, -⟩ := h ℚ χ τ hτ σ
  obtain ⟨f, hfD, hne⟩ := archNuclearityJet_span_false_key
  have hω := archNuclearityJet_span_false_omega χ hχ
  obtain ⟨n, hn⟩ := σ.surjective
    (⟨(-Complex.I, 0), archNuclearityJet_span_false_mult χ hχ τ hτ⟩ :
      Printed.ArchNuclearityJetIndex χ τ hτ)
  have hD : (Submodule.Quotient.mk f : Θ₀[ℚ, χ]) ∈ archNuclearityDenominator χ :=
    Submodule.subset_span ⟨f, by rw [eq_true hω]; exact hfD, rfl⟩
  have h0 : (archNuclearityDenominator χ).mkQ (Submodule.Quotient.mk f) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hD
  have hc := hd n (Submodule.Quotient.mk f)
  rw [h0, map_zero, hn] at hc
  unfold Printed.archNuclearityJet at hc
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply,
    iteratedDeriv_zero, schwartzBergmanEntireInclusion_apply] at hc
  apply hne
  have htw : ideleClassNormTwist χ (-Complex.I) = ideleClassNormTwist (1 : U[ℚ]) 0 := by
    have := ideleClassNormTwist_add_of_eq hχ (-Complex.I)
    simpa using this
  rw [← htw, ← ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f (-Complex.I)).2]
  exact hc.symm

/-- Paper: Equation (7.4.3.4), p. 368.
The unnormalized vertical integral in the printed jet formula is 2πi times the
inverse Mellin transform, so its logarithmic moment carries that factor. -/
def Printed.archNuclearityJet_apply : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F))
    (j : Printed.ArchNuclearityJetIndex χ τ hτ) (f : adelePolarSubspace F),
    let u := fun s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s)
    let moment := fun t : ℝ ↦ (Real.log t : ℂ) ^ j.val.2 * mellinInv 0 u t
    iteratedDeriv j.val.2 u j.val.1 =
      (2 * (Real.pi : ℂ) * Complex.I) * mellin moment j.val.1

/-- Paper: Equation (7.4.3.4), p. 368.
For ℚ and the trivial character, take the jet at −2 of order zero. Tensor
exp(−πx²) − 3 exp(−4πx²) + 2 exp(−16πx²) with the finite integral indicator.
The coefficients make the two polar moments vanish. The x² coefficient is
−21π, so the simple archimedean Mellin pole at −2 cancels the simple zeta zero
with nonzero result. The missing factor therefore changes the value.

The Lean proof uses instead the character `|·|^i` and the nonzero flat
zero-moment test of `archNuclearityJet_span_false_key`. Its zeta value at the
printed index `(−i, 0)` is nonzero, and `schwartzBergman_jet_eq_mellinInv_moment`
computes that jet as the unnormalized logarithmic moment itself, so the printed
factor `2πi` would force the nonzero value to vanish. -/
theorem Printed.archNuclearityJet_apply_false : ¬ Printed.archNuclearityJet_apply := by
  intro h
  obtain ⟨χ, hχ⟩ := archNuclearityJet_span_false_char
  let τ : ℝ≥0ˣ →ₜ* I[ℚ] := ⟨ratIdeleNormSection, ratIdeleNormSection_continuous⟩
  have hτ : RightInverse τ (ideleNorm ℚ) := ratIdeleNormSection_rightInverse
  obtain ⟨f, -, hne⟩ := archNuclearityJet_span_false_key
  let v : B := Z(χ, τ, hτ) (Submodule.Quotient.mk f : Θ₀[ℚ, χ])
  have hz : (v.val : ℂ → ℂ) = fun s ↦
      globalIdelicZFunction f.val (ideleClassNormTwist χ s) :=
    funext fun s ↦ ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f s).2
  have hmom := (schwartzBergman_jet_eq_mellinInv_moment v (-Complex.I) 0).2.2
  have heq := h ℚ χ τ hτ
    ⟨(-Complex.I, 0), archNuclearityJet_span_false_mult χ hχ τ hτ⟩ f
  simp only [iteratedDeriv_zero, pow_zero, one_mul] at hmom heq
  rw [← hz] at heq
  have hzpt : globalIdelicZFunction f.val (ideleClassNormTwist χ (-Complex.I)) =
      v.val (-Complex.I) := by
    simpa using (congrFun hz (-Complex.I)).symm
  rw [hzpt, hmom] at heq
  have h2 : (1 - 2 * (Real.pi : ℂ) * Complex.I) *
      mellin (fun t : ℝ ↦ mellinInv 0 v.val t) (-Complex.I) = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr heq
  have hc : (1 - 2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp at hre
  have hz0 : mellin (fun t : ℝ ↦ mellinInv 0 v.val t) (-Complex.I) = 0 :=
    (mul_eq_zero.mp h2).resolve_left hc
  have hu0 : v.val (-Complex.I) = 0 := by
    rw [hmom]
    exact hz0
  apply hne
  have htw : ideleClassNormTwist χ (-Complex.I) = ideleClassNormTwist (1 : U[ℚ]) 0 := by
    have := ideleClassNormTwist_add_of_eq hχ (-Complex.I)
    simpa using this
  rw [← htw]
  simpa [hz] using hu0

/-- Paper: Equation (7.4.3.14), p. 373. The printed gamma-pole sum with its
norm-character correction. -/
def Printed.archNuclearityTraceValue {F : Type*} [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F)) (φ : BruhatCompactSupport C[F]) : ℂ :=
  let invΓ := fun z ↦ (heckeGammaFactor χ z)⁻¹
  let Poles := {z : ℂ // 0 < analyticOrderAt invΓ z}
  let term := fun z : Poles ↦
    ((analyticOrderAt invΓ z.val).toNat : ℂ) * nuclearityTestMellin χ φ z.val
  let x := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let correction := if ω[F, χ] = 1 then
    nuclearityTestMellin (1 : U[F]) φ (-((x : ℂ) * Complex.I)) else 0
  (∑' z, term z) - correction

open MeasureTheory in
/-- A real radial test on the rational class group pairs positively with any continuous
weight positive on its log-norm window. -/
private theorem archNuclearityTraceValue_bump :
    ∃ (φ : BruhatCompactSupport C[ℚ]) (f : C[ℚ] → ℝ),
      (∀ g, φ.val g = (f g : ℂ)) ∧
      tsupport φ.val ⊆ {g : C[ℚ] | 1 < ((ideleClassNorm ℚ g).val : ℝ)} ∧
      ∀ w : ℝ → ℝ, Continuous w → (∀ t ∈ Ioo (1 / 4 : ℝ) (1 / 2), 0 < w t) →
        0 < ∫ g, f g * w (logIdeleClassNorm ℚ g) ∂ideleClassTamagawaMeasure ℚ := by
  let : MeasurableSpace C[ℚ] := borel _
  let : BorelSpace C[ℚ] := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure ℚ).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil ℚ).1
  let b : ContDiffBump (3 / 8 : ℝ) := ⟨1 / 32, 1 / 16, by norm_num, by norm_num⟩
  obtain ⟨φ, hφ⟩ := exists_normTest (F := ℚ) (fun t ↦ (b t : ℂ))
    (Complex.ofRealCLM.contDiff.comp b.contDiff) (b.hasCompactSupport.comp_left Complex.ofReal_zero)
  let l := logIdeleClassNorm ℚ
  have hl : Continuous l := (NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm ℚ).continuous)).log
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm ℚ g))).ne'
  have hs : tsupport φ.val ⊆ l ⁻¹' Metric.closedBall (3 / 8) (1 / 16) := by
    apply closure_minimal _ (Metric.isClosed_closedBall.preimage hl)
    intro g hg
    apply Metric.ball_subset_closedBall
    change l g ∈ Metric.ball (3 / 8) b.rOut
    rw [← b.support_eq]
    exact fun h ↦ hg ((hφ g).trans (Complex.ofReal_eq_zero.mpr h))
  have hwindow {g} (hg : g ∈ tsupport φ.val) : l g ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    have h := hs hg
    change dist (l g) (3 / 8) ≤ 1 / 16 at h
    rw [Real.dist_eq, abs_le] at h
    constructor <;> linarith
  refine ⟨φ, fun g ↦ b (l g), hφ, fun g hg ↦
    (Real.log_pos_iff (NNReal.coe_nonneg _)).mp (lt_trans (by norm_num) (hwindow hg).1), ?_⟩
  intro w hw hwpos
  have hc : HasCompactSupport (fun g ↦ b (l g)) := by
    have he : (fun g ↦ b (l g)) = Complex.re ∘ φ.val := funext fun g ↦ by simp [hφ, l]
    exact he ▸ (show HasCompactSupport φ.val from φ.property.2).comp_left Complex.zero_re
  let t := positiveRealLogEquiv.symm (Multiplicative.ofAdd (3 / 8 : ℝ))
  let g₀ : C[ℚ] := QuotientGroup.mk (ratIdeleNormSection t)
  have hcenter : l g₀ = 3 / 8 := by
    change Real.log ((ideleClassNorm ℚ g₀).val : ℝ) = _
    rw [show ideleClassNorm ℚ g₀ = t from ratIdeleNormSection_rightInverse t,
      ← positiveRealLogEquiv_apply, positiveRealLogEquiv.apply_symm_apply]
    rfl
  apply ((b.continuous.comp hl).mul (hw.comp hl)).integral_pos_of_hasCompactSupport_nonneg_ne_zero
    hc.mul_right (x := g₀)
  · intro g
    by_cases hz : b (l g) = 0
    · simp [hz]
    · have hmem : φ.val g ≠ 0 := (hφ g).trans_ne (Complex.ofReal_ne_zero.mpr hz)
      exact mul_nonneg b.nonneg (hwpos _ (hwindow (subset_tsupport _ hmem))).le
  · change b (l g₀) * w (l g₀) ≠ 0
    rw [hcenter, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact mul_ne_zero one_ne_zero (hwpos _ (by constructor <;> norm_num)).ne'

/-- The rational gamma factor in the norm-power chart is a translate of the trivial one. -/
private theorem archNuclearityTraceValue_gamma_shift (χ : U[ℚ])
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[ℚ]) Complex.I) (z : ℂ) :
    heckeGammaFactor χ z = heckeGammaFactor (1 : U[ℚ]) (z + Complex.I) := by
  rw [heckeGammaFactor_one,
    InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ),
    InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ),
    pow_one, pow_zero, mul_one]
  unfold heckeGammaFactor
  rw [Fintype.prod_unique]
  have hv : (default : InfinitePlace ℚ).IsReal :=
    (Subsingleton.elim (default : InfinitePlace ℚ) Rat.infinitePlace) ▸ Rat.isReal_infinitePlace
  simp only [dite_eq_left hv, archNuclearityJet_span_false_params χ hχ, Fin.val_zero, Nat.cast_zero,
    add_zero]

open MeasureTheory in
/-- The two correction terms differ because only the shifted correction has a
nonzero imaginary part. -/
private theorem archNuclearityTraceValue_corrections_ne
    (φ : BruhatCompactSupport C[ℚ]) (f : C[ℚ] → ℝ) (hφ : ∀ g, φ.val g = (f g : ℂ))
    (hpos : 0 < ∫ g, f g * Real.sin (logIdeleClassNorm ℚ g) ∂ideleClassTamagawaMeasure ℚ) :
    nuclearityTestMellin (1 : U[ℚ]) φ (-Complex.I) ≠ nuclearityTestMellin 1 φ 0 := by
  intro he
  let : MeasurableSpace C[ℚ] := borel _
  have him (g : C[ℚ]) :
      (φ.val g * ideleClassNormTwist (1 : U[ℚ]) (-Complex.I) g).im =
        -(f g * Real.sin (logIdeleClassNorm ℚ g)) := by
    rw [hφ, Complex.im_ofReal_mul]
    let n : ℝ := ((ideleClassNorm ℚ g).val : ℝ)
    have hn : 0 < n := NNReal.coe_pos.mpr (Units.zero_lt _)
    change f g * (1 * (n : ℂ) ^ (-Complex.I)).im = _
    rw [one_mul, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne'),
      ← Complex.ofReal_log hn.le, mul_neg, ← neg_mul, ← Complex.ofReal_neg,
      Complex.exp_ofReal_mul_I_im, Real.sin_neg, mul_neg]
  have him₀ : (nuclearityTestMellin (1 : U[ℚ]) φ 0).im = 0 := by
    rw [(nuclearityTestMellin_integrable (1 : U[ℚ]) φ).2, funext hφ,
      integral_complex_ofReal, Complex.ofReal_im]
  have hi := integral_im (𝕜 := ℂ) ((nuclearityTestMellin_integrable (1 : U[ℚ]) φ).1 (-Complex.I))
  change (∫ g, (φ.val g * ideleClassNormTwist (1 : U[ℚ]) (-Complex.I) g).im
    ∂ideleClassTamagawaMeasure ℚ) = (nuclearityTestMellin 1 φ (-Complex.I)).im at hi
  simp only [him, integral_neg, he, him₀, neg_eq_zero] at hi
  exact hpos.ne' hi

/-- Paper: Equation (7.4.3.14), p. 373.
The printed numerical expression changes when the same trivial norm-one
component is parametrized by the unitary norm power with exponent i.
A positive log-norm bump in (1/4,1/2) has real pole weights in both charts.
The correction in the shifted chart has strictly negative imaginary part. -/
theorem Printed.archNuclearityTraceValue_changes_in_norm_chart
    (τ : ℝ≥0ˣ →ₜ* I[ℚ]) (hτ : RightInverse τ (ideleNorm ℚ)) :
    ∃ (χ : U[ℚ]) (φ : BruhatCompactSupport C[ℚ]),
      (∀ g : C[ℚ], (χ g : ℂ) = ((((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ Complex.I)) ∧
      tsupport φ.val ⊆ {g : C[ℚ] | 1 < ((ideleClassNorm ℚ g).val : ℝ)} ∧
      Printed.archNuclearityTraceValue χ τ hτ φ ≠
        Printed.archNuclearityTraceValue (1 : U[ℚ]) τ hτ φ := by
  obtain ⟨χ, hχ⟩ := archNuclearityJet_span_false_char
  obtain ⟨φ, f, hφ, hs, hpos⟩ := archNuclearityTraceValue_bump
  refine ⟨χ, φ, archNuclearityJet_span_false_char_apply χ hχ, hs, ?_⟩
  let ord (ψ : U[ℚ]) := analyticOrderAt (fun z ↦ (heckeGammaFactor ψ z)⁻¹)
  have hord (z : ℂ) : ord χ z = ord 1 (z + Complex.I) := by
    simp only [ord, archNuclearityTraceValue_gamma_shift χ hχ]
    exact analyticOrderAt_comp_of_deriv_ne_zero (f := fun w ↦ (heckeGammaFactor (1 : U[ℚ]) w)⁻¹)
      (g := fun w : ℂ ↦ w + Complex.I)
      (analyticAt_id.add analyticAt_const) (by simp)
  have hM (z : ℂ) : nuclearityTestMellin χ φ z =
      nuclearityTestMellin 1 φ (z + Complex.I) := by
    have h := ideleClassNormTwist_add_of_eq hχ z
    simp only [zero_add, add_comm Complex.I z] at h
    simp only [nuclearityTestMellin, h]
  let poles (ψ : U[ℚ]) := {z : ℂ // 0 < ord ψ z}
  let term (ψ : U[ℚ]) (z : poles ψ) := ((ord ψ z.val).toNat : ℂ) * nuclearityTestMellin ψ φ z.val
  let e : poles χ ≃ poles 1 := (Equiv.addRight Complex.I).subtypeEquiv fun z ↦ by rw [hord]; rfl
  have hsum : ∑' z, term χ z = ∑' z, term 1 z := by
    rw [← e.tsum_eq (term 1)]
    apply tsum_congr
    intro z
    change ((ord χ z.val).toNat : ℂ) * nuclearityTestMellin χ φ z.val =
      ((ord 1 (z.val + Complex.I)).toNat : ℂ) * nuclearityTestMellin 1 φ (z.val + Complex.I)
    rw [hord, hM]
  let phase (ψ : U[ℚ]) := (existsUnique_ideleNormSection_character_phase ψ τ hτ).exists.choose
  have hp : phase χ = 1 := by
    apply (existsUnique_ideleNormSection_character_phase χ τ hτ).unique
      (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose_spec
    intro t
    rw [archNuclearityJet_span_false_char_apply χ hχ,
      show ideleClassNorm ℚ (QuotientGroup.mk (τ t)) = t from hτ t, Complex.ofReal_one, one_mul]
  have hp₀ : phase 1 = 0 := by
    apply (existsUnique_ideleNormSection_character_phase (1 : U[ℚ]) τ hτ).unique
      (existsUnique_ideleNormSection_character_phase (1 : U[ℚ]) τ hτ).exists.choose_spec
    intro t
    simp
  intro he
  change (∑' z, term χ z) - (if ω[ℚ, χ] = 1 then
    nuclearityTestMellin 1 φ (-((phase χ : ℂ) * Complex.I)) else 0) =
    (∑' z, term 1 z) - (if ω[ℚ, (1 : U[ℚ])] = 1 then
    nuclearityTestMellin 1 φ (-((phase 1 : ℂ) * Complex.I)) else 0) at he
  have hω₀ : ω[ℚ, (1 : U[ℚ])] = 1 := ContinuousMonoidHom.ext fun _ ↦ rfl
  simp only [hsum, ite_eq_left (archNuclearityJet_span_false_omega χ hχ), ite_eq_left hω₀,
    hp, hp₀, Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, neg_zero,
    sub_right_inj] at he
  exact archNuclearityTraceValue_corrections_ne φ f hφ
    (hpos Real.sin Real.continuous_sin fun t ht ↦
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_gt_three])) he

/-- Paper: Theorem 7.4.3.2(2), equation (7.4.3.14), p. 373.
The matrix trace in the derivative basis is the sum of its diagonal weights.
The printed correction to the gamma-pole series uses the norm to the power −ix₀. -/
def Printed.archNuclearity_trace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F))
    (φ : BruhatCompactSupport C[F]),
    tsupport φ.val ⊆ {g : C[F] | 1 < ((ideleClassNorm F g).val : ℝ)} →
    Printed.HasQuotientJetTrace (archNuclearityDenominator χ) (Printed.archNuclearityJet χ τ hτ)
      (Aθ(χ, τ, hτ, φ)) (Printed.archNuclearityTraceValue χ τ hτ φ)

/-- Paper: Theorem 7.4.3.2(2), equation (7.4.3.14), p. 373.
Over ℚ take χ = |·|^i and a nonzero nonnegative radial bump with log-norm
support in (1/4,1/2). The selected gamma poles have parameters −i−2n, giving
real diagonal values in any claimed derivative basis, by the product rule.
The pole sum is real and the printed correction has strictly negative imaginary part. -/
theorem Printed.archNuclearity_trace_false : ¬ Printed.archNuclearity_trace := by
  intro hall
  apply Printed.archNuclearityJet_basis_false
  intro F _ _ χ τ hτ
  let φ : BruhatCompactSupport C[F] := ⟨0, (bruhatCompactSupportSubmodule C[F]).zero_mem⟩
  have hφ : φ.val = (0 : C[F] → ℂ) := rfl
  exact (hall F χ τ hτ φ (by rw [hφ, tsupport_zero]; exact empty_subset _)).1

/-- Paper: Remark 7.4.3.3, p. 373.
The remark asserts that the operator induced on the quotient is nonnuclear for
every test with the preceding support condition. Its argument uses the strong dual. -/
def Printed.archNuclearityStrongDual_not_nuclear : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (τ : ℝ≥0ˣ →ₜ* I[F]) (hτ : RightInverse τ (ideleNorm F))
    (φ : BruhatCompactSupport C[F]),
    tsupport φ.val ⊆ {g : C[F] | 1 < ((ideleClassNorm F g).val : ℝ)} →
    Printed.HasNonnuclearQuotientAction (archNuclearityDenominator χ) (Aθ(χ, τ, hτ, φ))

/-- A zero endomorphism of any space with a uniformity has a nuclear presentation:
zero coefficients and functionals, with the Banach disc `{0}`. -/
private theorem archNuclearityStrongDual_not_nuclear_false_zero
    {E : Type*} [AddCommGroup E] [Module ℂ E] {_ : UniformSpace E}
    (T : E →L[ℂ] E) (hT : T = 0) : Nonempty (NuclearPresentation T) := by
  let S := Submodule.span ℂ ({0} : Set E)
  have hsub : ∀ x : S, x = 0 := by
    rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp
  have hpre : ((↑) ⁻¹' ({0} : Set E) : Set S) = univ := by
    ext x
    simp [hsub x]
  have bB : Balanced ℂ ((↑) ⁻¹' ({0} : Set E) : Set S) := hpre ▸ balanced_univ
  have cB : Convex ℝ ((↑) ⁻¹' ({0} : Set E) : Set S) := hpre ▸ convex_univ
  have aB : Absorbent ℝ ((↑) ⁻¹' ({0} : Set E) : Set S) := hpre ▸ absorbent_univ
  have hss : ∀ x y : WithLocalSeminorm (gaugeSeminorm bB cB aB), x = y :=
    fun x y ↦ (hsub x).trans (hsub y).symm
  have hdisc : IsBanachDisc ({0} : Set E) :=
    { bounded := fun _ hV ↦ absorbs_zero_iff.mpr (mem_of_mem_nhds hV)
      balanced := bB
      convex := cB
      absorbent := aB
      separated := ⟨fun x y h ↦ (h (hss x y)).elim⟩
      complete := ⟨fun {f} _ ↦ ⟨0, fun U hU ↦ by
        have hU' : U = univ := Set.eq_univ_of_forall fun y ↦ hss 0 y ▸ mem_of_mem_nhds hU
        exact hU' ▸ Filter.univ_mem⟩⟩ }
  exact ⟨{ coeff := fun _ ↦ 0
           functional := fun _ ↦ 0
           disc := {0}
           isBanachDisc := hdisc
           vector := fun _ ↦ 0
           vector_mem := fun _ ↦ by simp
           summable_coeff := by simp
           equicontinuous := fun U hU ↦ Filter.Eventually.of_forall fun _ _ ↦ by
             simpa using refl_mem_uniformity hU
           hasSum := fun x ↦ by simp [hT] }⟩

/-- An endomorphism of a quotient module is zero when its graph is described by convolution
with the zero function, through a linear transform of representatives. -/
private theorem archNuclearityStrongDual_not_nuclear_false_action
    {N : Type*} {_ : AddCommGroup N} {_ : Module ℂ N} (P : Submodule ℂ N) (p : Submodule ℂ P)
    {_ : TopologicalSpace (P ⧸ p)}
    {G : Type*} {_ : CommGroup G} {_ : TopologicalSpace G} {_ : MeasurableSpace G}
    (μ : MeasureTheory.Measure G)
    (Θ : N → C(G, ℂ)) (hΘ : IsLinearMap ℂ Θ) (φv : G → ℂ) (hφv : φv = 0)
    (A : (P ⧸ p) →L[ℂ] (P ⧸ p))
    (hA : ∀ f g : P, A (Submodule.Quotient.mk f) = Submodule.Quotient.mk g ↔
      (Θ g.val : G → ℂ) = lcaConvolution μ φv (Θ f.val)) : A = 0 := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  rw [zero_apply]
  induction x using Quotient.inductionOn' with
  | h f =>
    refine ((hA f 0).mpr ?_).trans (Submodule.Quotient.mk_zero _)
    rw [ZeroMemClass.coe_zero, hΘ.map_zero, ContinuousMap.coe_zero, hφv]
    funext y
    simp [lcaConvolution]

/-- An endomorphism of a quotient induced by the zero operator is zero. -/
private theorem archNuclearityStrongDual_not_nuclear_false_induced
    {M : Type*} {_ : AddCommGroup M} {_ : Module ℂ M} {_ : TopologicalSpace M}
    (D : Submodule ℂ M) {_ : TopologicalSpace (M ⧸ D)}
    (A : M →L[ℂ] M) (hA : A = 0) (T : (M ⧸ D) →L[ℂ] (M ⧸ D))
    (hT : ∀ x : M, T (D.mkQ x) = D.mkQ (A x)) : T = 0 := by
  refine ContinuousLinearMap.ext fun q ↦ ?_
  obtain ⟨x, rfl⟩ := D.mkQ_surjective q
  rw [hT x, hA, zero_apply, map_zero, zero_apply]

/-- Paper: Remark 7.4.3.3, p. 373.
Take F = ℚ, the trivial character, and the zero Bruhat test. Its support is empty
and every multiplier derivative vanishes. The induced action and transpose have
rank zero and admit nuclear presentations. -/
theorem Printed.archNuclearityStrongDual_not_nuclear_false :
    ¬ Printed.archNuclearityStrongDual_not_nuclear := by
  intro h
  let τ : ℝ≥0ˣ →ₜ* I[ℚ] := ⟨ratIdeleNormSection, ratIdeleNormSection_continuous⟩
  have hτ : RightInverse τ (ideleNorm ℚ) := ratIdeleNormSection_rightInverse
  let φ : BruhatCompactSupport C[ℚ] := ⟨0, (bruhatCompactSupportSubmodule C[ℚ]).zero_mem⟩
  have hφ : φ.val = (0 : C[ℚ] → ℂ) := rfl
  obtain ⟨T, hT, hnot⟩ := h ℚ 1 τ hτ φ (by rw [hφ, tsupport_zero]; exact empty_subset _)
  have hspec := (exists_polarThetaNuclearityAction (1 : U[ℚ]) τ hτ φ).choose_spec.2
  have hA : (exists_polarThetaNuclearityAction (1 : U[ℚ]) τ hτ φ).choose = 0 := by
    refine archNuclearityStrongDual_not_nuclear_false_action _ _ _ _ ?_ _ ?_ _ hspec
    · exact homogeneousAdelicTheta_isLinear _
    · exact hφ
  have hT0 : T = 0 :=
    archNuclearityStrongDual_not_nuclear_false_induced _ _ hA T hT
  apply hnot
  apply archNuclearityStrongDual_not_nuclear_false_zero
  exact hT0

/-- Paper: Theorem 7.4.3.1(3)–(5), proof before (7.4.3.12), p. 371.
As printed: the images of the tests with both polar moments zero have
codimension two in the source and target homogeneous theta spaces.
This is the codimension assertion. See `globalThetaPolarValues_vanish_on_isotype_iff`,
`globalThetaPolarValues_surjective_on_trivial_isotype` and ERRATA F136. -/
def Printed.archNuclearity_polar_codimension_two : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (χ : U[F]),
    Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) →
    ∀ hχ : ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) ∈
        unramifiedOutside F S,
      let hω : NormOneCharacterUnramifiedOutside (ω[F, χ]) S := ⟨⟨_, hχ⟩, fun _ ↦ rfl⟩
      let ωₛ := sLocalNormOneCharacter S (ω[F, χ]) hω
      let Kₛ := LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ωₛ)
      let Pₛ := (sAdelePolarSubspace F S).map Kₛ.mkQ
      Module.finrank ℂ (SLocalHomogeneousThetaSpace F S ωₛ ⧸ Pₛ) = 2 ∧
        Module.finrank ℂ (GlobalHomogeneousThetaSpace F (ω[F, χ]) ⧸
          globalPolarFreeThetaSubmodule (ω[F, χ])) = 2

/-- The class of the rational idele equal to `-1` at one finite place and `1` elsewhere is
not the identity: a principal idele with archimedean component one is one. Copied from the
private lemma `strongCoprimality_false_neg_one_ne` of `Sec5_Printed.lean`. -/
private theorem archNuclearity_polar_codimension_two_false_neg_one_ne
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (-1) ≠ 1 := by
  intro h
  obtain ⟨r, hr⟩ := (QuotientGroup.eq_one_iff _).mp h
  have hval := congrArg Units.val hr
  have hinf := congrArg (fun x : 𝔸[ℚ] ↦ x.1 Rat.infinitePlace) hval
  change algebraMap ℚ Rat.infinitePlace.Completion r.val = 1 at hinf
  have hr₁ : r.val = 1 := (algebraMap ℚ Rat.infinitePlace.Completion).injective
    (hinf.trans (map_one _).symm)
  have hfin := congrArg (fun x : 𝔸[ℚ] ↦ x.2 v) hval
  change algebraMap ℚ (v.adicCompletion ℚ) r.val =
    RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 ℚ) ↦ w.adicCompletionIntegers ℚ) v
      ((-1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) v at hfin
  rw [RestrictedProduct.mulSingle_eq_same, hr₁, map_one, Units.val_neg, Units.val_one] at hfin
  have : (1 : ℚ) = -1 := (algebraMap ℚ (v.adicCompletion ℚ)).injective
    (by simpa only [map_neg, map_one] using hfin)
  norm_num at this

/-- When a submodule surjects onto a quotient, the quotient by its image is zero, so its
rank is not two. -/
private theorem archNuclearity_polar_codimension_two_false_finrank
    {M : Type*} [AddCommGroup M] [Module ℂ M] (K P : Submodule ℂ M)
    (h : Surjective (K.mkQ.comp P.subtype)) :
    Module.finrank ℂ ((M ⧸ K) ⧸ P.map K.mkQ) ≠ 2 := by
  have htop : P.map K.mkQ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨p, rfl⟩ := h x
    exact Submodule.mem_map_of_mem p.property
  have hsub : Subsingleton ((M ⧸ K) ⧸ P.map K.mkQ) :=
    Submodule.Quotient.subsingleton_iff.mpr htop
  rw [Module.finrank_zero_of_subsingleton]
  norm_num

/-- Paper: Theorem 7.4.3.1(3)–(5), proof before (7.4.3.12), p. 371.
Take F = ℚ, S with just the finite place over 5, and the even quadratic
character modulo 5. The idèle with component 2 at 5 and 1 elsewhere has norm
one and acts by −1 on the homogeneous component. If T is translation by
this idèle, (f − Tf)/2 has the class of f and both polar moments vanish.
The polar image is the whole target component, of codimension zero. -/
theorem Printed.archNuclearity_polar_codimension_two_false :
    ¬ Printed.archNuclearity_polar_codimension_two := by
  intro h
  let v : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨3, Nat.prime_three⟩
  let g₀ : C[ℚ] := IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (-1)
  have hg₀ : g₀ ∈ (ideleClassNorm ℚ).ker := by
    rw [MonoidHom.mem_ker, ideleClassNorm_ofAdicCompletion]
    apply Units.ext
    apply NNReal.coe_injective
    change ‖((-1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ = 1
    rw [Units.val_neg, Units.val_one, norm_neg, norm_one]
  -- Characters separate the points of the idele classes, so one of them moves `g₀`.
  obtain ⟨χ, hχ⟩ : ∃ χ : U[ℚ], χ g₀ ≠ 1 := by
    by_contra hall
    push Not at hall
    exact archNuclearity_polar_codimension_two_false_neg_one_ne v
      ((pontryaginDual_pairing_separates (G := C[ℚ])).1
        (funext fun χ ↦ (hall χ).trans (map_one χ).symm))
  -- It is unramified outside a finite set, which can be enlarged to kill the Picard group.
  obtain ⟨S₀, hS₀⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)),
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) ∈ unramifiedOutside ℚ S :=
    mem_iUnion.mp ((iUnion_unramifiedOutside ℚ).symm ▸ mem_univ _)
  obtain ⟨S, hS, hpic⟩ := (picard_uniformization (F := ℚ) S₀).1
  have hω : ω[ℚ, χ] ≠ 1 := fun h1 ↦ hχ (DFunLike.congr_fun h1 ⟨g₀, hg₀⟩)
  have h2 := (h ℚ S χ hpic (fun w hw ↦ hS₀ w fun hw₀ ↦ hw (hS hw₀))).2
  -- On a norm-one component that is not trivial the polar tests reach every class.
  exact archNuclearity_polar_codimension_two_false_finrank _ _
    (globalConverse_nontrivial_exact _ hω).surjective h2

/-- Paper: Theorem 7.4.3.1(3)–(5), proof before (7.4.3.12), p. 371.
Each class of the flat tensor space displayed in (7.4.3.1) has a unique
S-local function in the tensor space (5.3.4.1) representing it. The graph
requires an additive Schwartz representative to which the theta map applies.
The prose following (7.4.3.1) also describes an archimedean moment condition.
The zero class used in F137 belongs to both readings. -/
def Printed.archNuclearity_existsUnique_localFlatRepresentative : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (χ : U[F]),
    Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) →
    ∀ hχ : ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) ∈
        unramifiedOutside F S,
      let hω : NormOneCharacterUnramifiedOutside (ω[F, χ]) S := ⟨⟨_, hχ⟩, fun _ ↦ rfl⟩
      let ωₛ := sLocalNormOneCharacter S (ω[F, χ]) hω
      let Kₛ := LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ωₛ)
      let K := LinearMap.ker (homogeneousAdelicThetaLinearMap F (ω[F, χ]))
      let flat := Submodule.span ℂ {f : SAdeleRing F S → ℂ |
        ∃ (h : archimedeanFlatSchwartz (ι := {v : InfinitePlace F // v.IsReal})
            (κ := {v : InfinitePlace F // v.IsComplex}))
          (g : (v : S) → SchwartzBruhat (v.val.adicCompletion F)ˣ), ∀ a, f a =
            h.val (fun v ↦ InfinitePlace.Completion.ringEquivRealOfIsReal v.property (a.1 v.val),
              fun v ↦ InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property (a.1 v.val)) *
              ∏ v : S, (if hv : a.2 v ≠ 0 then g v (Units.mk0 (a.2 v) hv) else 0)}
      ∀ x ∈ (globalArchimedeanFlatTests F).map K.mkQ,
        ∃! f : flat, ∃ (test : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
            (y : SLocalHomogeneousThetaSpace F S ωₛ),
          (∀ a, test (Multiplicative.ofAdd a) = f.val a) ∧
            sLocalHomogeneousThetaToGlobal hω y = x ∧
            sLocalHomogeneousThetaPrincipalValue (Finset.Subset.refl S) ωₛ y = Kₛ.mkQ test

/-- An odd `S`-adelic test has zero `S`-local homogeneous theta transform: in its `S`-unit
sum the terms of a unit and of its negative cancel. -/
private theorem archNuclearity_existsUnique_localFlatRepresentative_false_odd
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ω : PontryaginDual (MonoidHom.ker (sIdeleQuotientNorm F S)))
    (test : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (hodd : ∀ a : SAdeleRing F S,
      test (Multiplicative.ofAdd (-a)) = -test (Multiplicative.ofAdd a)) :
    test ∈ LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω) := by
  have hθ (c : SIdeleQuotient F S) : sLocalAdelicThetaOnClasses F S test c = 0 := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
    change ∑' ξ : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ,
      test (Multiplicative.ofAdd (Units.val (sUnitEmbedding F S ξ * x))) = 0
    have hneg (ξ : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ) :
        test (Multiplicative.ofAdd (Units.val (sUnitEmbedding F S (-ξ) * x))) =
          -test (Multiplicative.ofAdd (Units.val (sUnitEmbedding F S ξ * x))) := by
      rw [← hodd]
      simp
    have hs := (Equiv.neg ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ).tsum_eq
      (fun ξ : ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ ↦
        test (Multiplicative.ofAdd (Units.val (sUnitEmbedding F S ξ * x))))
    simp only [Equiv.neg_apply, hneg, tsum_neg] at hs
    exact self_eq_neg.mp hs.symm
  rw [LinearMap.mem_ker]
  ext g
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply]
  simp only [hθ, zero_mul, MeasureTheory.integral_zero]
  rfl

/-- Over `ℚ` with no finite place, a Schwartz function of the mixed archimedean coordinates
is a Schwartz–Bruhat function of the `S`-adele. -/
private theorem archNuclearity_existsUnique_localFlatRepresentative_false_test
    (k : SchwartzMap (({v : InfinitePlace ℚ // v.IsReal} → ℝ) ×
      ({v : InfinitePlace ℚ // v.IsComplex} → ℂ)) ℂ) :
    ∃ test : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)),
      ∀ a : SAdeleRing ℚ ∅, test (Multiplicative.ofAdd a) =
        k (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ a.1) := by
  have hinf := (mem_archimedeanSchwartzBruhat_iff (F := ℚ)
    (fun x ↦ k (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x))).mpr ⟨k, fun _ ↦ rfl⟩
  let fI : SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)) := ⟨_, hinf⟩
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv (F := ℚ) ∅
  exact ⟨_, fun a ↦ (he fI (fun _ ↦ 0) a).trans (by simp; rfl)⟩

/-- A Schwartz function of the mixed archimedean coordinates of `ℚ` that is odd, flat along
the coordinate walls and equal to one at the point with all coordinates one: the difference
of a bump around that point and its reflection. -/
private theorem archNuclearity_existsUnique_localFlatRepresentative_false_bump :
    ∃ k ∈ archimedeanFlatSchwartz (ι := {v : InfinitePlace ℚ // v.IsReal})
        (κ := {v : InfinitePlace ℚ // v.IsComplex}),
      (∀ u, k (-u) = -k u) ∧ k (fun _ ↦ 1, fun _ ↦ 1) = 1 := by
  let Coord := ({v : InfinitePlace ℚ // v.IsReal} → ℝ) × ({v : InfinitePlace ℚ // v.IsComplex} → ℂ)
  let c : Coord := (fun _ ↦ 1, fun _ ↦ 1)
  let b : ContDiffBump c := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let k : Coord → ℂ := fun u ↦ ((b u : ℝ) : ℂ) - ((b (-u) : ℝ) : ℂ)
  have hkc : ContDiff ℝ (⊤ : ℕ∞) k :=
    (Complex.ofRealCLM.contDiff.comp b.contDiff).sub
      (Complex.ofRealCLM.contDiff.comp (b.contDiff.comp contDiff_neg))
  let A : Set Coord := Metric.closedBall c (1 / 2) ∪ Metric.closedBall (-c) (1 / 2)
  have hzero : ∀ u, u ∉ A → k u = 0 := by
    intro u hu
    have h1 : b u = 0 := b.zero_of_le_dist
      (not_le.mp fun h ↦ hu (Or.inl (Metric.mem_closedBall.mpr h))).le
    have h2 : b (-u) = 0 := b.zero_of_le_dist (by
      rw [← dist_neg_neg, neg_neg]
      exact (not_le.mp fun h ↦ hu (Or.inr (Metric.mem_closedBall.mpr h))).le)
    simp only [k, h1, h2, Complex.ofReal_zero, sub_zero]
  have hks : HasCompactSupport k :=
    HasCompactSupport.intro ((isCompact_closedBall c _).union (isCompact_closedBall (-c) _)) hzero
  have hts : tsupport k ⊆ A :=
    closure_minimal (fun u hu ↦ by_contra fun hn ↦ hu (hzero u hn))
      (Metric.isClosed_closedBall.union Metric.isClosed_closedBall)
  -- A ball of radius one half around a point with unit coordinates misses every wall.
  have hwall : ∀ c' : Coord, (∀ i, ‖c'.1 i‖ = 1) → (∀ j, ‖c'.2 j‖ = 1) →
      ∀ u ∈ Metric.closedBall c' (1 / 2), ¬ ((∃ i, u.1 i = 0) ∨ (∃ j, u.2 j = 0)) := by
    intro c' hc1 hc2 u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu
    rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · have h1 : ‖(u - c').1 i‖ ≤ ‖u - c'‖ := (norm_le_pi_norm _ i).trans (norm_fst_le _)
      have h2 : (u - c').1 i = -c'.1 i := by
        change u.1 i - c'.1 i = -c'.1 i
        rw [hi, zero_sub]
      rw [h2, norm_neg, hc1] at h1
      linarith
    · have h1 : ‖(u - c').2 j‖ ≤ ‖u - c'‖ := (norm_le_pi_norm _ j).trans (norm_snd_le _)
      have h2 : (u - c').2 j = -c'.2 j := by
        change u.2 j - c'.2 j = -c'.2 j
        rw [hj, zero_sub]
      rw [h2, norm_neg, hc2] at h1
      linarith
  refine ⟨hks.toSchwartzMap hkc, mem_archimedeanFlatSchwartz_of_tsupport _ ?_, fun u ↦ ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro u hu hw
    rcases hts hu with hu' | hu'
    · exact hwall c (fun _ ↦ norm_one) (fun _ ↦ norm_one) u hu' hw
    · exact hwall (-c) (fun _ ↦ (norm_neg (1 : ℝ)).trans norm_one)
        (fun _ ↦ (norm_neg (1 : ℂ)).trans norm_one) u hu' hw
  · change k (-u) = -k u
    simp only [k, neg_neg, neg_sub]
  · change k c = 1
    have h1 : b c = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    have h2 : b (-c) = 0 := by
      apply b.zero_of_le_dist
      let i₀ : {v : InfinitePlace ℚ // v.IsReal} := ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
      have h3 : ‖(-c - c).1 i₀‖ ≤ ‖-c - c‖ := (norm_le_pi_norm _ i₀).trans (norm_fst_le _)
      have h4 : (-c - c).1 i₀ = -2 := by
        change (-1 : ℝ) - 1 = -2
        norm_num
      rw [h4] at h3
      norm_num at h3
      change (1 / 2 : ℝ) ≤ dist (-c) c
      rw [dist_eq_norm]
      linarith
    simp only [k, h1, h2, Complex.ofReal_one, Complex.ofReal_zero, sub_zero]

/-- Paper: Theorem 7.4.3.1(3)–(5), proof before (7.4.3.12), p. 371.
Take F = ℚ, S consisting of the real place, χ = 1 and the zero global class.
For a nonzero smooth bump h supported in (2, 3), use the local tests 0 and
x ↦ h(x) − h(−x). The latter is flat at zero and has integral zero.
Its S-unit theta sum at u is f(u) + f(−u) = 0. Finite principal value with
the empty selection is the identity, so both tests represent the zero class. -/
theorem Printed.archNuclearity_existsUnique_localFlatRepresentative_false :
    ¬ Printed.archNuclearity_existsUnique_localFlatRepresentative := by
  intro h
  have hpic : Subsingleton (CommRing.Pic (((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) :
      Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)) := by
    rw [Finset.coe_empty, integer_empty]
    let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
    let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
    let := IsPrincipalIdealRing.of_surjective i i.surjective
    infer_instance
  have hχ : ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (1 : U[ℚ])) ∈
      unramifiedOutside ℚ ∅ := (mem_unramifiedOutside_iff ℚ ∅ _).mpr fun _ _ _ ↦ rfl
  obtain ⟨k, hflat, hodd, hone⟩ := archNuclearity_existsUnique_localFlatRepresentative_false_bump
  obtain ⟨test, htest⟩ := archNuclearity_existsUnique_localFlatRepresentative_false_test k
  have hodd' : ∀ a : SAdeleRing ℚ ∅,
      test (Multiplicative.ofAdd (-a)) = -test (Multiplicative.ofAdd a) := by
    intro a
    rw [htest, htest]
    change k (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ (-a.1)) = _
    rw [map_neg, hodd]
  obtain ⟨f, -, huniq⟩ := h ℚ ∅ 1 hpic hχ 0 (Submodule.zero_mem _)
  -- The zero function and the odd bump both represent the zero class, through `y = 0`.
  have e0 := huniq 0 ⟨0, 0, fun _ ↦ rfl, map_zero _, (map_zero _).trans (map_zero _).symm⟩
  have e1 := huniq ⟨fun a ↦ k (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ a.1),
      Submodule.subset_span ⟨⟨k, hflat⟩, fun _ ↦ 0, fun a ↦ by simp⟩⟩ (by
    refine ⟨test, 0, htest, map_zero _, ?_⟩
    rw [map_zero]
    exact ((Submodule.Quotient.mk_eq_zero _).mpr
      (archNuclearity_existsUnique_localFlatRepresentative_false_odd ℚ ∅ _ test hodd')).symm)
  have hval := congrArg (fun g ↦ g.val
    ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm (fun _ ↦ 1, fun _ ↦ 1), 0)) (e1.trans e0.symm)
  change k (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ
    ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm (fun _ ↦ 1, fun _ ↦ 1))) = 0 at hval
  rw [RingEquiv.apply_symm_apply, hone] at hval
  exact one_ne_zero hval

open MeasureTheory in
/-- Paper: Theorem 7.4.3.2(2), proof, equation (7.4.3.15), p. 373.
As printed: for any a, b > 0, the right upward integral minus the left upward
integral of the test Mellin transform times the gamma logarithmic derivative,
divided by 2πi, sums the positive gamma pole multiplicities in the open strip.
The ordinary line integrals must exist. See `archNuclearity_trace` and ERRATA F140. -/
def Printed.archNuclearity_gammaContour : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (φ : BruhatCompactSupport C[F]),
    tsupport φ.val ⊆ {g : C[F] | 1 < ((ideleClassNorm F g).val : ℝ)} →
    ∀ (a b : ℝ), 0 < a → 0 < b →
      let Γ := heckeGammaFactor χ
      let Φ := nuclearityTestMellin χ φ
      let integrand := fun z ↦ Φ z * (deriv Γ z / Γ z)
      let poles := {z : ℂ // z.re ∈ Ioo (-a) b ∧ 0 < gammaOrder(χ, z)}
      let onLine (σ y : ℝ) := integrand ((σ : ℂ) + (y : ℂ) * Complex.I)
      Integrable (onLine (-a)) ∧ Integrable (onLine b) ∧
        HasSum (fun z : poles ↦ (gammaOrder(χ, z.val) : ℂ) * Φ z.val)
          ((verticalLineIntegral integrand b - verticalLineIntegral integrand (-a)) /
            (2 * (Real.pi : ℂ) * Complex.I))

open Filter Asymptotics MeasureTheory in
/-- A continuous multiplier nonzero at a simple pole leaves a vertical integrand
whose norm dominates a positive multiple of `1 / |t|`.
This is the simple-pole argument from `Ch07_SchauderBasesZeta/Sec1a_Printed`. -/
private theorem archNuclearity_gammaContour_simplePole {Φ Z : ℂ → ℂ} {σ : ℝ}
    (hZ : MeromorphicAt Z (σ : ℂ)) (hp : meromorphicOrderAt Z (σ : ℂ) = -1)
    (hΦ : Continuous (fun t : ℝ ↦ Φ ((σ : ℂ) + t * Complex.I))) (hne : Φ (σ : ℂ) ≠ 0) :
    ¬ Complex.VerticalIntegrable (Φ * Z) σ := by
  obtain ⟨g, hg, hg₀, he⟩ := (meromorphicOrderAt_eq_int_iff (n := -1) hZ).mp hp
  let l (t : ℝ) : ℂ := σ + t * Complex.I
  have hl : Tendsto l (𝓝 (0 : ℝ)) (𝓝 (σ : ℂ)) := by
    have hc : Continuous l := by dsimp [l]; fun_prop
    simpa [l] using hc.tendsto 0
  have hle : Tendsto l (𝓝[≠] (0 : ℝ)) (𝓝[≠] (σ : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hl.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin (α := ℝ) (a := 0) (s := {0}ᶜ)] with t ht
    simpa [l] using ht
  let c := Φ (σ : ℂ) * g (σ : ℂ)
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr (mul_ne_zero hne hg₀)
  have hlim : Tendsto (fun t ↦ Φ (l t) * g (l t)) (𝓝 0) (𝓝 c) := by
    have hΦlim : Tendsto (fun t ↦ Φ (l t)) (𝓝 0) (𝓝 (Φ (σ : ℂ))) := by
      simpa [l] using hΦ.tendsto 0
    exact hΦlim.mul (hg.continuousAt.tendsto.comp hl)
  have hbound := (hlim.norm.eventually (lt_mem_nhds (half_lt_self hpos))).filter_mono
    (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
  have hO : (fun t : ℝ ↦ (t - 0)⁻¹) =O[𝓝[≠] 0] (fun t ↦ (Φ * Z) (l t)) := by
    refine isBigO_iff''.mpr ⟨_, half_pos hpos, ?_⟩
    filter_upwards [hbound, hle.eventually he] with t ht heq
    have hprod : (Φ * Z) (l t) = (l t - (σ : ℂ)) ^ (-1 : ℤ) • (Φ (l t) * g (l t)) := by
      rw [Pi.mul_apply, heq, smul_eq_mul, smul_eq_mul, mul_left_comm]
    simp only [hprod, norm_smul, zpow_neg_one, norm_inv,
      show l t - (σ : ℂ) = t * Complex.I by simp [l], norm_mul, Complex.norm_I, mul_one, Complex.norm_real, sub_zero]
    rw [mul_comm (‖c‖ / 2)]
    simpa only [norm_mul] using mul_le_mul_of_nonneg_left ht.le (inv_nonneg.mpr (norm_nonneg t))
  intro hi
  exact not_intervalIntegrable_of_sub_inv_isBigO_punctured hO zero_ne_one left_mem_uIcc
    (hi.intervalIntegrable (a := 0) (b := 1))

/-- The rational gamma logarithmic derivative has order minus one at minus two. -/
private theorem archNuclearity_gammaContour_order :
    meromorphicOrderAt (logDeriv (heckeGammaFactor (1 : U[ℚ]))) (-2) = -1 := by
  let Γ := heckeGammaFactor (1 : U[ℚ])
  let τ : ℝ≥0ˣ →ₜ* I[ℚ] := ⟨ratIdeleNormSection, ratIdeleNormSection_continuous⟩
  have hτ : RightInverse τ (ideleNorm ℚ) := ratIdeleNormSection_rightInverse
  have hle : archNuclearityMultiplicity (1 : U[ℚ]) τ hτ (-2) ≤
      (analyticOrderAt Γ⁻¹ (-2)).toNat := Nat.sub_le _ _
  rw [(archNuclearityMultiplicity_rat_one τ hτ).2] at hle
  have ha : AnalyticAt ℂ Γ⁻¹ (-2) := (differentiable_inv_heckeGammaFactor (1 : U[ℚ])).analyticAt _
  have hp : meromorphicOrderAt Γ (-2) < 0 := by
    rw [← inv_inv Γ, meromorphicOrderAt_inv, ha.meromorphicOrderAt_eq]
    cases ho : analyticOrderAt Γ⁻¹ (-2) with
    | top => simp [ho] at hle
    | coe n =>
      simp [ho] at hle
      simp only [ENat.map_natCast]
      exact_mod_cast (show -(n : ℤ) < 0 by omega)
  exact meromorphicOrderAt_logDeriv_eq_neg_one hp.ne hp.ne_top

open MeasureTheory in
/-- On a fixed vertical line, the absolute value of the norm power is independent of
height, so dominated convergence gives continuity of the Mellin transform. -/
private theorem archNuclearity_gammaContour_mellin_continuous (φ : BruhatCompactSupport C[ℚ])
    (σ : ℝ) : Continuous (fun t : ℝ ↦ nuclearityTestMellin (1 : U[ℚ]) φ
      ((σ : ℂ) + t * Complex.I)) := by
  let : MeasurableSpace C[ℚ] := borel _
  let W (z : ℂ) (g : C[ℚ]) := φ.val g * ideleClassNormTwist (1 : U[ℚ]) z g
  have hint (z : ℂ) : Integrable (W z) (ideleClassTamagawaMeasure ℚ) :=
    (nuclearityTestMellin_integrable 1 φ).1 z
  let n (g : C[ℚ]) : ℝ := ((ideleClassNorm ℚ g).val : ℝ)
  have hn (g) : 0 < n g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hW (z : ℂ) (g : C[ℚ]) : W z g = φ.val g * (n g : ℂ) ^ z := by
    change φ.val g * (1 * (n g : ℂ) ^ z) = _
    rw [one_mul]
  apply continuous_of_dominated (bound := fun g ↦ ‖W (σ : ℂ) g‖)
  · exact fun t ↦ (hint _).aestronglyMeasurable
  · intro t
    apply Filter.Eventually.of_forall
    intro g
    change ‖W _ g‖ ≤ ‖W _ g‖
    simp [hW, Complex.norm_cpow_eq_rpow_re_of_pos (hn g)]
  · exact (hint _).norm
  · apply Filter.Eventually.of_forall
    intro g
    change Continuous (fun t : ℝ ↦ W ((σ : ℂ) + t * Complex.I) g)
    simp only [hW]
    exact continuous_const.mul ((continuous_const_cpow' (Complex.ofReal_ne_zero.mpr (hn g).ne')).comp
      (continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)))

/-- Paper: Theorem 7.4.3.2(2), proof, equation (7.4.3.15), p. 373.
For F = ℚ, χ = 1 and a = b = 1, take a nonzero nonnegative radial bump
supported at norms in (2, 3). The only enclosed gamma pole is at zero, with
logarithmic derivative residue −1. The normalized integral gives −Φ(0)
and the printed sum gives Φ(0) > 0. The Lean proof uses a = 2, which puts a pole on the left line,
and a radial test with strictly positive Mellin value at −2. -/
theorem Printed.archNuclearity_gammaContour_false : ¬ Printed.archNuclearity_gammaContour := by
  intro hall
  obtain ⟨φ, f, hφ, hs, hpos⟩ := archNuclearityTraceValue_bump
  let Γ := heckeGammaFactor (1 : U[ℚ])
  let Φ := nuclearityTestMellin (1 : U[ℚ]) φ
  have hΦ : Φ (-2) ≠ 0 := by
    let w (t : ℝ) := Real.exp (t * (-2))
    have hweight (g : C[ℚ]) : ideleClassNormTwist (1 : U[ℚ]) (-2) g =
        (w (logIdeleClassNorm ℚ g) : ℂ) := by
      let n : ℝ := ((ideleClassNorm ℚ g).val : ℝ)
      have hn : 0 < n := NNReal.coe_pos.mpr (Units.zero_lt _)
      change 1 * (n : ℂ) ^ (-2 : ℂ) = (Real.exp (Real.log n * (-2)) : ℂ)
      rw [one_mul, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne'),
        ← Complex.ofReal_log hn.le, Complex.ofReal_exp, Complex.ofReal_mul]
      norm_num
    change (∫ g, φ.val g * ideleClassNormTwist (1 : U[ℚ]) (-2) g ∂ideleClassTamagawaMeasure ℚ) ≠ 0
    simp only [hφ, hweight, ← Complex.ofReal_mul, integral_complex_ofReal, ne_eq, Complex.ofReal_eq_zero]
    exact (hpos w (by fun_prop) fun t _ ↦ Real.exp_pos _).ne'
  apply archNuclearity_gammaContour_simplePole (σ := -2) (Φ := Φ) (Z := logDeriv Γ)
    (by simpa using (meromorphic_heckeGammaFactor (1 : U[ℚ]) (-2)).logDeriv)
    (by simpa using archNuclearity_gammaContour_order)
    (archNuclearity_gammaContour_mellin_continuous φ (-2)) (by simpa using hΦ)
  exact (hall ℚ 1 φ hs 2 1 (by norm_num) one_pos).1

end RiemannMasullo
