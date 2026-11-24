module
import Lean
import all RiemannMasullo.AppC_LCTVS.Sec3a
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
import all RiemannMasullo.Ch10_TraceSpectral.Sec3
import all RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch09_HardySobolev.Sec3
import all RiemannMasullo.Ch09_HardySobolev.Sec2
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2a
import all RiemannMasullo.AppA_AlgebraicNT.Sec1
/-!
# A sufficient coordinate estimate for Theorem 10.3.2.1(1)

Masullo, pp. 453–455 and issue #6993. All operators below act on the actual
spectral Sobolev quotient. The Mellin transform is sampled on circles of one
fixed radius, independent of the zero, its vertical height and the jet order.

* `allMoments_ratio` compares every lower-order coordinate functional with
  its top coordinate, with the factorial and binomial weights of translation.
* `allMoments_composed_norm` bounds the norm of every coordinate after the
  transpose of the actual test convolution by four times the Mellin circle
  bound times its original norm.
* `stripRectangles_of_summable_coordinate_conditioning` and
  `stripRectangles_of_polynomial_coordinate_conditioning` give sufficient
  criteria for trace-norm convergence in the Cauchy sense. Any injection
  into the quadrant is allowed. Both the strict endpoint cutoff and arbitrarily
  large interior jets are included.

The last theorem assumes a multiplicity-weighted count, a height-dependent
bound on coordinate projection norms and a Mellin bound for one fixed test.
An estimate uniform over the actual biorthogonal coordinates is open.
-/

noncomputable section
open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology
namespace RiemannMasullo
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 270000
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
section
open Metric
variable {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [T2Space G] (μ : Measure G) [IsLocallyFiniteMeasure μ]
    (l : G → ℝ) (φ : G → ℂ)
private def radialMoment (z : ℂ) (q : ℕ) :=
  ∫ g, φ g * Complex.exp (z * (l g : ℂ)) * (l g:ℂ)^q ∂μ
private theorem radialMoment_deriv (hl : Continuous l) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (z : ℂ) (q : ℕ) :
    HasDerivAt (fun w ↦ radialMoment μ l φ w q) (radialMoment μ l φ z (q+1)) z := by
  let K := tsupport φ
  let F (w : ℂ) (g : G) := φ g * Complex.exp (w*(l g:ℂ)) * (l g:ℂ)^q
  let D (w : ℂ) (g : G) := φ g * Complex.exp (w*(l g:ℂ)) * (l g:ℂ)^(q+1)
  have hF (w) : Continuous (F w) := by dsimp [F]; fun_prop
  have hD : Continuous (fun p : ℂ × G ↦ D p.1 p.2) := by dsimp [D]; fun_prop
  obtain ⟨B,hB⟩ := ((isCompact_closedBall z 1).prod hc).exists_bound_of_continuousOn hD.continuousOn
  let bound := K.indicator (fun _ ↦ B)
  have hbound : Integrable bound μ :=
    (integrable_indicator_iff hc.measurableSet).mpr (integrableOn_const hc.measure_lt_top.ne)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := D)
    (bound := bound) (Metric.closedBall_mem_nhds z zero_lt_one)
    (Eventually.of_forall (fun w ↦ (hF w).aestronglyMeasurable))
    ((hF z).integrable_of_hasCompactSupport (hc.mul_right.mul_right))
    ((hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall (fun g w hw ↦ ?_)) hbound (Eventually.of_forall (fun g w _ ↦ ?_))).2
  · by_cases hg : g ∈ K
    · rw [show bound g = B from indicator_of_mem hg _]
      exact hB (w,g) ⟨hw,hg⟩
    · simp [bound,D,hg,image_eq_zero_of_notMem_tsupport hg]
  · simpa only [F,D,pow_succ,id_eq] using
      (((((hasDerivAt_id w).mul_const (l g:ℂ)).cexp).const_mul (φ g)).mul_const ((l g:ℂ)^q) |>.congr_deriv
        (by simp; ring))
private theorem radialMoment_cauchy (hl : Continuous l) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (z : ℂ) (q : ℕ) {R M : ℝ} (hR : 0 < R)
    (hM : ∀ w ∈ sphere z R, ‖radialMoment μ l φ w 0‖ ≤ M) :
    ‖radialMoment μ l φ z q‖ ≤ q.factorial * M / R^q := by
  have hder (n : ℕ) : iteratedDeriv n (fun w ↦ radialMoment μ l φ w 0) = (fun w ↦ radialMoment μ l φ w n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      funext w
      rw [iteratedDeriv_succ,ih,(radialMoment_deriv μ l φ hl hφ hc w n).deriv]
  have hol : Differentiable ℂ (fun w ↦ radialMoment μ l φ w 0) :=
    fun w ↦ (radialMoment_deriv μ l φ hl hφ hc w 0).differentiableAt
  simpa only [hder] using Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le q hR hol.diffContOnCl hM
#print axioms radialMoment_cauchy
end
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
private theorem rectangles_of_rankOne_majorant {J Z : Type*}
    (A : H →L[ℂ] H) (x : J → H) (L : J → StrongDual ℂ H) (N : Z → ℕ)
    (j : (z : Z) → Fin (N z) → J) (e : Z ↪ ℕ × ℕ)
    (g : Z → ℝ) (hg : Summable g)
    (h : ∀ z, (∑ m : Fin (N z), ‖(L (j z m)).comp A‖ * ‖x (j z m)‖) ≤ g z) :
    SpectralRectanglesTraceCauchy (fun i ↦ spectralConvolutionFiniteSum A x L
      (((Finset.Iic i.1).product (Finset.Iic i.2)).preimage e e.injective.injOn) N j) := by
  classical
  let T (z : Z) (m : Fin (N z)) : nuclearEndomorphisms H :=
    ⟨((L (j z m)).comp A).smulRight (x (j z m)), smulRight_mem_nuclearEndomorphisms _ _⟩
  let R (z : Z) := ∑ m, T z m
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let : NormedAddCommGroup (nuclearEndomorphisms H) :=
    NormedAddCommGroup.ofCore (traceNorm_normedSpaceCore (H := H))
  let : SeminormedAddCommGroup (nuclearEndomorphisms H) :=
    (inferInstance : NormedAddCommGroup (nuclearEndomorphisms H)).toSeminormedAddCommGroup
  let : MetricSpace (nuclearEndomorphisms H) := NormedAddCommGroup.toMetricSpace
  let : PseudoMetricSpace (nuclearEndomorphisms H) := MetricSpace.toPseudoMetricSpace
  let : UniformSpace (nuclearEndomorphisms H) := PseudoMetricSpace.toUniformSpace
  have hR (z : Z) : ‖R z‖ ≤ g z := by
    change traceNorm (∑ m, T z m) ≤ g z
    apply (traceNorm_sum_le Finset.univ (T z)).trans
    simpa only [T,traceNorm_smulRight] using h z
  have hc := cauchySeq_finset_of_norm_bounded_eventually hg (Eventually.of_forall hR)
  intro ε hε
  obtain ⟨S,hS⟩ := (Metric.cauchySeq_iff (u := fun s : Finset Z ↦ ∑ z ∈ s, R z)).mp hc ε hε
  let i := S.sup (fun z ↦ (e z).1)
  let k := S.sup (fun z ↦ (e z).2)
  let E (v : ℕ × ℕ) := ((Finset.Iic v.1).product (Finset.Iic v.2)).preimage e e.injective.injOn
  have hsub (v : ℕ × ℕ) (hv : (i,k) ≤ v) : S ≤ E v := by
    intro z hz
    simpa [E] using And.intro ((Finset.le_sup hz).trans hv.1) ((Finset.le_sup hz).trans hv.2)
  have heq (v : ℕ × ℕ) : (∑ z ∈ E v, R z).val = spectralConvolutionFiniteSum A x L (E v) N j := by
    simp only [R,T,Submodule.coe_sum,spectralConvolutionFiniteSum]
  refine ⟨(i,k),fun v w hv hw ↦ ⟨(∑ z ∈ E v, R z) - (∑ z ∈ E w, R z), ?_,?_⟩⟩
  · exact congrArg₂ (·-·) (heq _) (heq _)
  · have hdist (T U : nuclearEndomorphisms H) : dist T U = traceNorm (T-U) := by
      rw [dist_eq_norm]
      rfl
    have hr := hS (E v) (hsub v hv) (E w) (hsub w hw)
    rwa [hdist] at hr
#print axioms rectangles_of_rankOne_majorant
end
variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "W(" l ", " r ", " s ")" =>
  CompactIntervalSobolev μ𝔽 (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) l r s
local notation "Θ(" a ", " hI ", " hs ")" => globalThetaSobolev F a hI hs
local notation "Q(" a ", " hI ", " hs ")" => spectralSobolevQuotient F a hI hs
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation (G := C𝔽) m𝔽)

variable (a : ℝ)
local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

variable {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)

local notation "logNorm" => (logIdeleClassNorm F)
local notation "D" => spectralSobolevDualEmbedding F a (hStrip(hα)) hs₀(hs)
local notation "raw(" χ ", " j ")" =>
  spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "jet(" z ", " m ")" => ⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩
local notation "J(" χ ")" => SpectralStripJetIndex (F := F) χ a α s

private def mass (α s b x : ℝ) :=
  Real.exp (2*b*x) / intervalSobolevDensity (-α) α s x
private def moment (α s b : ℝ) (k : ℕ) (x : ℝ) :=
  |x|^(2*k) * mass α s b x
private theorem mass_pos {α s b x : ℝ} (hα : 0 ≤ α) : 0 < mass α s b x :=
  div_pos (Real.exp_pos _) (symmIntervalSobolevDensity_pos hα _ _)
private theorem mass_shift {α s b : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hb : b ∈ Icc (-α) α)
    (x d : ℝ) : mass α s b x ≤ Real.exp ((4*α+s)*|d|) * mass α s b (x+d) := by
  let ρ := intervalSobolevDensity (-α) α s
  have h₀ : 0 < ρ x := symmIntervalSobolevDensity_pos hα _ _
  have h₁ : 0 < ρ (x+d) := symmIntervalSobolevDensity_pos hα _ _
  have hdx : ρ (x+d) ≤ (Real.exp (α*|d|) * Real.exp (|d| *(s/2)))^2 * ρ x := by
    have h := intervalSobolevDensity_add_le (-α) α s hs d x
    rw [add_comm d x] at h
    refine h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ _) h₀.le)
    apply mul_le_mul _ _ (by positivity) (Real.exp_pos _).le
    · apply max_le <;> apply Real.exp_le_exp.mpr
      · calc -α*d = α*(-d) := by ring
             _ ≤ _ := mul_le_mul_of_nonneg_left (neg_le_abs _) hα
      · exact mul_le_mul_of_nonneg_left (le_abs_self _) hα
    · rw [Real.exp_mul]
      exact Real.rpow_le_rpow (by positivity) (by simpa [add_comm] using Real.add_one_le_exp |d|) (by positivity)
  have hbd : -(b*d) ≤ α*|d| := calc
    _ ≤ |b*d| := neg_le_abs _
    _ = |b| *|d| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (abs_le.mpr hb) (abs_nonneg _)
  dsimp only [mass]
  change Real.exp (2*b*x) / ρ x ≤ _ * (Real.exp (2*b*(x+d)) / ρ (x+d))
  rw [←mul_div_assoc,div_le_div_iff₀ h₀ h₁]
  calc
    _ ≤ Real.exp (2*b*x)*((Real.exp (α*|d|) * Real.exp (|d| *(s/2)))^2 * ρ x) :=
      mul_le_mul_of_nonneg_left hdx (Real.exp_pos _).le
    _ = Real.exp (2*b*x + 2*(α*|d|+|d| *(s/2)))*ρ x := by
      rw [←Real.exp_add, sq, ←Real.exp_add, mul_comm (2:ℝ) _,two_mul,
        ←mul_assoc,←Real.exp_add]
    _ ≤ _ := by
      rw [←Real.exp_add]
      apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr _) h₀.le
      nlinarith only [hbd]
private theorem moment_integrable {α s b : ℝ} {k : ℕ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (h : -α < b ∧ b < α ∨ (b = -α ∨ b = α) ∧ 2*(k:ℝ)+1<s) :
    Integrable (moment α s b k) := by
  apply (spectralStripJet_integrable hα hs h).congr (.of_forall fun x ↦ ?_)
  have he : |x|^(2*k) = x^(2*k) := by rw [pow_mul,pow_mul,sq_abs]
  simp only [moment,mass,he,symmIntervalSobolevDensity_eq hα,Real.exp_sub,div_eq_mul_inv,mul_inv_rev]
  ring
private theorem moment_compare {α s b : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hb : b ∈ Icc (-α) α)
    (k m : ℕ) (hk : k ≤ m) (hi : Integrable (moment α s b m)) :
    let q := m-k
    ((m.choose k:ℝ) * (q.factorial:ℝ))^2 * (∫ x, moment α s b k x) ≤
      2 * Real.exp ((4*α+s)*q) * (∫ x, moment α s b m x) := by
  intro q
  let c : ℝ := (m.choose k:ℝ) * (q.factorial:ℝ)
  let A := Real.exp ((4*α+s)*q)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hm (x : ℝ) : 0 ≤ moment α s b m x := mul_nonneg (by positivity) (mass_pos hα).le
  have hq : (q.factorial:ℝ) ≤ (q:ℝ)^q := by exact_mod_cast Nat.factorial_le_pow q
  have hp (x : ℝ) : c*|x|^k ≤ (|x|+q)^m := by
    rw [add_pow]
    apply le_trans _ (Finset.single_le_sum (f := fun i ↦ |x|^i*(q:ℝ)^(m-i)*(m.choose i:ℝ))
      (fun i _ ↦ by positivity) (Finset.mem_range.mpr (by omega : k < m+1)))
    calc c*|x|^k = (|x|^k * (q.factorial:ℝ))*(m.choose k:ℝ) := by dsimp [c]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by positivity)) (by positivity)
  have part (x d : ℝ) (hd : |d| = q) (hxd : |x+d|=|x|+q) :
      c^2*moment α s b k x ≤ A*moment α s b m (x+d) := by
    have hw := mass_shift hα hs hb x d
    rw [hd] at hw
    calc
      _ = (c*|x|^k)^2 * mass α s b x := by unfold moment; rw [show 2*k=k*2 by omega,pow_mul]; ring
      _ ≤ ((|x|+q)^m)^2 * (A * mass α s b (x+d)) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) (hp x) _) hw (mass_pos hα).le (by positivity)
      _ = _ := by unfold moment; rw [hxd,show 2*m=m*2 by omega,pow_mul]; ring
  have point (x : ℝ) : c^2*moment α s b k x ≤
      A*moment α s b m (x+q) + A*moment α s b m (x+ -(q:ℝ)) := by
    by_cases hx : 0 ≤ x
    · exact (part x q (abs_of_nonneg (Nat.cast_nonneg _)) (by rw [abs_of_nonneg (by positivity),abs_of_nonneg hx])).trans
        (le_add_of_nonneg_right (mul_nonneg hA (hm _)))
    · apply le_trans _ (le_add_of_nonneg_left (mul_nonneg hA (hm _)))
      apply part
      · rw [abs_neg,abs_of_nonneg (Nat.cast_nonneg _)]
      · rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) q]),abs_of_nonpos (le_of_not_ge hx)]; ring
  have i₁ := (hi.comp_add_right (q:ℝ)).const_mul A
  have i₂ := (hi.comp_add_right (-(q:ℝ))).const_mul A
  calc
    _ = ∫ x : ℝ, c^2*moment α s b k x := (integral_const_mul ..).symm
    _ ≤ ∫ x : ℝ, (A*moment α s b m (x+q) + A*moment α s b m (x+ -(q:ℝ))) :=
      integral_mono_of_nonneg (ae_of_all _ (fun x ↦ mul_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (mass_pos hα).le))) (i₁.add i₂) (ae_of_all _ point)
    _ = _ := by rw [integral_add i₁ i₂,integral_const_mul,integral_const_mul,integral_add_right_eq_self,integral_add_right_eq_self]; ring
#print axioms moment_compare
private theorem admissible_moment_condition (α s b : ℝ) (n k : ℕ)
    (h : k < spectralStripMultiplicity α s b n) :
    -α < b ∧ b < α ∨ (b = -α ∨ b = α) ∧ 2*(k:ℝ)+1<s := by
  unfold spectralStripMultiplicity at h
  split_ifs at h with hi hb
  · exact Or.inl hi
  · exact Or.inr ⟨hb,by linarith [((lt_spectralBoundaryMultiplicity s n k).mp h).2]⟩
  · omega
private theorem allMoments_ratio
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (f : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (z : Z(χ, α)) (m k : Fin (N(χ, α, s, z))) (hk : k ≤ m) :
    let q := m.val-k.val
    (m.val.choose k.val:ℝ) * (q.factorial:ℝ) * ‖f (jet(z,k))‖ ≤
      2 * (Real.exp ((4*α+s)/2))^q * ‖f (jet(z,m))‖ := by
  intro q
  let mod : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  have hmod : IsModulation (G := C𝔽) mod := ⟨isProperMap_ideleClassNorm F,ideleClassNorm_ne_one (F := F)⟩
  let ν := canonicalModulatedHaar (G := C𝔽) mod hmod
  have hmeas := existsUnique_canonicalModulatedHaar (G := C𝔽) mod hmod
  let : ν.IsHaarMeasure := hmeas.exists.choose_spec.1
  let A : ℝ := Measure.haarScalarFactor μ𝔽 ν
  have hA : 0 ≤ A := NNReal.coe_nonneg _
  let b := z.val.2.1
  let p (n : Fin (N(χ, α, s, z))) := ‖f (jet(z,n))‖
  have hm (n : Fin (N(χ, α, s, z))) : p n ^ 2 = A * ∫ y, moment α s b n.val y := by
    let j : J(χ) := jet(z,n)
    have hd := (spectralSobolevDualEmbedding_isometry_range (F := F) a (hStrip(hα)) hs₀(hs)).1.dist_eq (f j) 0
    have he : ‖D (f j)‖ = ‖f j‖ := by simpa only [map_zero,dist_eq_norm,sub_zero] using hd
    change ‖f j‖^2 = _
    rw [←he,hj,spectralStripJet_norm_sq χ hα hs₀(hs) j ν rfl]
    apply congrArg (A * ·)
    apply integral_congr_ae (.of_forall fun y ↦ ?_)
    change Real.exp (2*b*y-2*α*|y|)*y^(2*n.val)*((1+y^2)^(s/2))⁻¹ = _
    have hy : |y|^(2*n.val) = y^(2*n.val) := by rw [pow_mul,pow_mul,sq_abs]
    simp only [moment,mass,hy,symmIntervalSobolevDensity_eq hα,Real.exp_sub,div_eq_mul_inv,mul_inv_rev]
    ring
  have hi : Integrable (moment α s b m.val) := by
    apply moment_integrable hα hs₀(hs)
    exact admissible_moment_condition α s b _ m.val m.isLt
  have c := moment_compare hα hs₀(hs) z.property.1 k.val m.val hk hi
  let R := Real.exp ((4*α+s)/2)
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have he : Real.exp ((4*α+s)*q) = (R^q)^2 := by
    dsimp [R]
    rw [← Real.exp_nat_mul, sq, ← Real.exp_add]
    congr 1; ring
  change ((m.val.choose k.val:ℝ) * (q.factorial:ℝ))^2 * _ ≤ 2 * Real.exp ((4*α+s)*q) * _ at c
  rw [he] at c
  have hsq : ((m.val.choose k.val:ℝ)*(q.factorial:ℝ)*p k)^2 ≤
      2*(R^q)^2*(p m)^2 := by
    rw [mul_pow, hm, hm]
    linarith only [mul_le_mul_of_nonneg_left c hA]
  have hpos : 0 ≤ 2*R^q*p m := by dsimp [p]; positivity
  change _ ≤ 2*R^q*p m
  nlinarith only [hsq, hpos, (sq_nonneg (R^q * p m))]
#print axioms allMoments_ratio
section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (μ : Measure G) [μ.IsHaarMeasure] (n : G →* ℝ≥0ˣ) (hn : Continuous n)
    (l r s₀ : ℝ) (hl : l ≤ r) (hs₀ : 0 ≤ s₀)
local notation "Uraw" => CompactIntervalSobolev μ (fun g : G ↦ Real.log ((n g).val:ℝ)) l r s₀
local notation "ncont" => (⟨n,hn⟩ : G →ₜ* ℝ≥0ˣ)
private abbrev rawTranslation : G →* (Uraw →L[ℂ] Uraw) :=
  hardySobolevTranslation μ ncont l r s₀ hl hs₀
private theorem rawTranslation_apply (g : G) (v : Uraw) :
    (rawTranslation μ n hn l r s₀ hl hs₀ g v : G → ℂ) =ᵐ[μ] (fun x ↦ v (g⁻¹*x)) :=
  hardySobolevTranslation_apply μ ncont l r s₀ hl hs₀ g v
private abbrev rawAction (φ : BruhatCompactSupport G) : Uraw →L[ℂ] Uraw :=
  hardySobolevTestAction μ ncont l r s₀ hl hs₀ φ
private theorem rawTranslation_pettis (φ : BruhatCompactSupport G)
    (v : Uraw) (ℓ : StrongDual ℂ Uraw) :
    ℓ (rawAction μ n hn l r s₀ hl hs₀ φ v) =
      ∫ g, ℓ (φ.val g • rawTranslation μ n hn l r s₀ hl hs₀ g v) ∂μ := by
  let τ := rawTranslation μ n hn l r s₀ hl hs₀
  have hP := bruhatRegularizedAction_apply μ τ
    (exists_hardySobolevTranslation μ ncont l r s₀ hl hs₀).choose_spec.2 φ v
  exact congrArg (fun p : PettisWeakCompletion Uraw ↦
    (show Module.Dual ℂ (StrongDual ℂ Uraw) from p) ℓ) hP.2
end

private theorem scalar_integral_identity {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (u v w : G → ℂ) (c y : ℂ) :
    (∫ g, u g * ((v g * w g * c) * y) ∂μ) = c * (∫ g, u g * v g * w g ∂μ) * y := by
  rw [←integral_const_mul,←integral_mul_const]
  apply integral_congr_ae (.of_forall fun g ↦ ?_)
  ring

private theorem integrated_product_congr {G : Type*} [MeasurableSpace G] (μ : Measure G)
    {u v : G → ℂ} (j : G → ℂ) (h : u =ᵐ[μ] v) :
    (∫ x, u x * j x ∂μ) = ∫ x, v x * j x ∂μ :=
  integral_congr_ae (h.mono fun x hx ↦ congrArg (· * j x) hx)

private theorem allMoments_translate (η : PontryaginDual C𝔽) (b t : ℝ)
    (m : ℕ) (v : W(-α, α, s))
    (hint : ∀ i ≤ m, Integrable (fun x ↦ v x * spectralZeroJet (F := F) η b t i x) μ𝔽)
    (g : C𝔽) :
    ∫ y : C𝔽, (v : C𝔽 → ℂ) (g⁻¹*y) * spectralZeroJet (F := F) η b t m y ∂μ𝔽 =
      ∑ i : Fin (m+1), (ideleClassNormTwist (F := F) η (shift(b,t)) g *
        (logNorm g:ℂ)^(m-i.val) * (m.choose i.val:ℂ)) *
        ∫ y, v y * spectralZeroJet (F := F) η b t i.val y ∂μ𝔽 := by
  let T := ideleClassNormTwist (F := F) η ((b : ℂ) + (t : ℂ) * Complex.I)
  let L (y : C𝔽) : ℂ := logNorm y
  let c (i : ℕ) := T g * L g ^ (m - i) * (m.choose i : ℂ)
  have hlog (y : C𝔽) : L (g * y) = L y + L g := by
    dsimp only [L, logIdeleClassNorm]
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)
      (NNReal.coe_ne_zero.2 (ideleClassNorm F y).ne_zero), Complex.ofReal_add, add_comm]
  have hsum (y : C𝔽) : v y * spectralZeroJet (F := F) η b t m (g * y) =
      ∑ i ∈ Finset.range (m + 1), c i * (v y * spectralZeroJet (F := F) η b t i y) := by
    change v y * (T (g * y) * L (g * y) ^ m) = _
    rw [map_mul, hlog, add_pow]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change v y * (T g * T y * (L y ^ i * L g ^ (m - i) * (m.choose i : ℂ))) =
      (T g * L g ^ (m - i) * (m.choose i : ℂ)) * (v y * (T y * L y ^ i))
    ring
  let J := spectralZeroJet (F := F) η b t m
  let H (y : C𝔽) := v (g⁻¹ * y) * J y
  calc
    _ = ∫ y, H y ∂μ𝔽 := rfl
    _ = ∫ y, H (g * y) ∂μ𝔽 := (integral_mul_left_eq_self H g).symm
    _ = ∫ y, v y * J (g * y) ∂μ𝔽 := by simp only [H, inv_mul_cancel_left]
    _ = _ := by
      simp_rw [show ∀ y, v y * J (g * y) = _ from hsum]
      rw [integral_finsetSum _ fun i hi ↦ (hint i (Finset.mem_range_succ_iff.mp hi)).const_mul (c i)]
      simp_rw [integral_const_mul]
      exact (Fin.sum_univ_eq_sum_range (fun i ↦ c i * ∫ y, v y * spectralZeroJet (F := F) η b t i y ∂μ𝔽) _).symm
private theorem allMoments_action
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (f : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽) (z : Z(χ, α)) (m : Fin (N(χ, α, s, z)))
    (u : Q(a, hStrip(hα), hs₀(hs))) :
    f (jet(z, m)) (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ u) =
      ∑ i : Fin (m.val+1), (m.val.choose i.val : ℂ) *
        (∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1,z.val.2.2)) g *
           (logNorm g:ℂ)^(m.val-i.val) ∂μ𝔽) *
        f (jet(z, (⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ : Fin (N(χ, α, s, z))))) u := by
  let θ : Submodule ℂ W(-α,α,s) := globalThetaSobolev F (α := -α) (β := α) (s := s) a (hStrip(hα)) hs₀(hs)
  obtain ⟨v, hv⟩ := θ.mkQ_surjective u
  let J (i : ℕ) := spectralZeroJet (χ z.val.1) z.val.2.1 z.val.2.2 i
  let j : J(χ) := jet(z, m)
  let mod : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  let τ := rawTranslation (G := C𝔽) μ𝔽 (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous (-α) α s (hStrip(hα)) hs₀(hs)
  let ℓ := (f j).comp θ.mkQL
  let η := ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2))
  have heval (j : J(χ)) (w : W(-α, α, s)) :=
    spectralStripConvolution_jet_eval (a := a) hα hs χ j (f j) (hj j) w
  have hint (i : ℕ) (hi : i ≤ m.val) : Integrable (fun y ↦ v y * J i y) μ𝔽 := by
    let k : Fin (N(χ, α, s, z)) := ⟨i, hi.trans_lt m.isLt⟩
    exact (heval (jet(z, k)) v).1
  let idx (i : Fin (m.val+1)) : Fin (N(χ, α, s, z)) := ⟨i.val,(Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩
  let y (i : Fin (m.val+1)) := f (jet(z,idx i)) u
  let h (i : Fin (m.val+1)) (g : C𝔽) := (η g * (logNorm g:ℂ)^(m.val-i.val) * (m.val.choose i.val:ℂ))*y i
  have hi (i : Fin (m.val+1)) : (∫ x, v x * J i.val x ∂μ𝔽) = y i :=
    (heval (jet(z,idx i)) v).2.symm.trans (congrArg (f (jet(z,idx i))) hv)
  have hτ (g : C𝔽) : ℓ (τ g v) = ∑ i : Fin (m.val+1), h i g := by
    have haeFormula := rawTranslation_apply (G := C𝔽) μ𝔽 (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous (-α) α s (hStrip(hα)) hs₀(hs) g
    have hae := haeFormula v
    have hshift := integrated_product_congr μ𝔽 (J m.val) hae
    have ht := allMoments_translate (F := F) (α := α) (s := s) (χ z.val.1) z.val.2.1 z.val.2.2 m.val v hint g
    refine (heval j (τ g v)).2.trans (hshift.trans (ht.trans ?_))
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg ((η g * (logNorm g:ℂ)^(m.val-i.val) * (m.val.choose i.val:ℂ)) * ·) (hi i)
  have hφ : Continuous φ.val := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hg (i : Fin (m.val+1)) : Integrable (fun g : C𝔽 ↦ φ.val g * h i g) μ𝔽 := by
    have hl : Continuous (fun g : C𝔽 ↦ (logNorm g:ℂ)) := Complex.continuous_ofReal.comp (continuous_logModule' (G := C𝔽) mod)
    exact (hφ.mul (((η.continuous.mul (hl.pow _)).mul continuous_const).mul continuous_const)).integrable_of_hasCompactSupport
      (show HasCompactSupport φ.val from φ.property.2).mul_right
  have pettis := rawTranslation_pettis (G := C𝔽) μ𝔽 (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous (-α) α s (hStrip(hα)) hs₀(hs) φ
  have he := pettis v ℓ
  have conv := spectralConvolution_mkQ (F := F) a (hStrip(hα)) hs₀(hs) φ
  simp only at conv
  calc
    _ = ℓ (rawAction (G := C𝔽) μ𝔽 (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous (-α) α s (hStrip(hα)) hs₀(hs) φ v) :=
      (congrArg (fun w ↦ f j (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ w)) hv.symm).trans
        (congrArg (f j) (conv v))
    _ = ∫ g, ℓ (φ.val g • τ g v) ∂μ𝔽 := he
    _ = ∫ g, ∑ i : Fin (m.val+1), φ.val g * h i g ∂μ𝔽 := integral_congr_ae (.of_forall fun g ↦ by
      exact (map_smul ℓ (φ.val g) (τ g v)).trans
        ((congrArg (φ.val g * ·) (hτ g)).trans (Finset.mul_sum ..)))
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ ↦ hg i)]
      apply Finset.sum_congr rfl
      intro i _
      change (∫ g : C𝔽, φ.val g * ((η g * (logNorm g:ℂ)^(m.val-i.val) * (m.val.choose i.val:ℂ)) * y i) ∂μ𝔽) =
        (m.val.choose i.val:ℂ)*(∫ g : C𝔽, φ.val g * η g * (logNorm g:ℂ)^(m.val-i.val) ∂μ𝔽)*y i
      exact scalar_integral_identity μ𝔽 φ.val η (fun g ↦ (logNorm g:ℂ)^(m.val-i.val)) _ _
#print axioms allMoments_action
private theorem translate_mellin_zero (χ : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽)
    (w : ℂ) (q : ℕ) :
    (∫ g : C𝔽, φ.val g * ideleClassNormTwist χ w g * (logNorm g:ℂ)^q ∂μ𝔽) =
      radialMoment μ𝔽 logNorm (fun g ↦ φ.val g * (χ g:ℂ)) w q := by
  apply integral_congr_ae (.of_forall fun g ↦ ?_)
  have hp : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have he : ideleClassNormTwist χ w g = (χ g:ℂ) * Complex.exp (w*(logNorm g:ℂ)) := by
    change (χ g:ℂ) * ((((ideleClassNorm F g).val : ℝ):ℂ)^w) = _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),←Complex.ofReal_log hp.le]
    exact congrArg ((χ g:ℂ) * ·) (congrArg Complex.exp (mul_comm _ _))
  rw [he]; ring
private theorem allMoments_geometric (n : ℕ) :
    ∑ i : Fin (n+1), (1/2 : ℝ)^(n-i.val) ≤ 2 := by
  have eq : (∑ i : Fin (n+1), (1/2 : ℝ)^(n-i.val)) =
      ∑ i ∈ Finset.range (n+1), (1/2 : ℝ)^i := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (1/2:ℝ)^(n-i)) (n+1)]
    simpa using Finset.sum_range_reflect (fun i ↦ (1/2 : ℝ)^i) (n+1)
  rw [eq]
  have hs := hasSum_geometric_of_lt_one (show 0 ≤ (1/2:ℝ) by norm_num) (show (1/2:ℝ) < 1 by norm_num)
  exact (hs.summable.sum_le_tsum _ (fun _ _ ↦ by positivity)).trans_eq (by rw [hs.tsum_eq]; norm_num)
private theorem allMoments_scaled {c f r u v M t : ℝ} (q : ℕ) (hr : 0 < r) (hM : 0 ≤ M)
    (_hf : 0 ≤ f) (hc : 0 ≤ c) (hv : 0 ≤ v) (_hu : 0 ≤ u)
    (hw : c*f*v ≤ 2*r^q*u) (ht : t ≤ f*M/(2*r)^q) :
    c*t*v ≤ (1/2:ℝ)^q * (2*M*u) := by
  have hrq : 0 < r^q := pow_pos hr _
  have h₂ : (0:ℝ) < 2^q := by positivity
  calc
    _ ≤ c*(f*M/(2*r)^q)*v := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hc) hv
    _ = c*f*v * (M/(2^q*r^q)) := by rw [mul_pow]; ring
    _ ≤ (2*r^q*u)*(M/(2^q*r^q)) := mul_le_mul_of_nonneg_right hw (by positivity)
    _ = _ := by rw [div_pow]; field_simp; ring

set_option maxHeartbeats 800000 in
private theorem allMoments_norm_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (c : ℂ) (f : StrongDual ℂ V) : ‖c • f‖ = ‖c‖*‖f‖ := norm_smul c f

private theorem allMoments_composed_norm
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (f : J(χ) → StrongDual ℂ Q(a,hStrip(hα),hs₀(hs)))
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ,j)))
    (φ : BruhatCompactSupport C𝔽) (z : Z(χ,α)) (m : Fin (N(χ,α,s,z))) (M : ℝ) (hM : 0 ≤ M)
    (hfreq : ∀ w ∈ Metric.sphere (shift(z.val.2.1,z.val.2.2)) (2*Real.exp ((4*α+s)/2)),
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖ ≤ M) :
    ‖(f (jet(z,m))).comp (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ)‖ ≤
      4*M*‖f (jet(z,m))‖ := by
  let R := Real.exp ((4*α+s)/2)
  let w₀ := shift(z.val.2.1,z.val.2.2)
  let t (q : ℕ) := ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w₀ g * (logNorm g:ℂ)^q ∂μ𝔽
  let idx (i : Fin (m.val+1)) : Fin (N(χ,α,s,z)) := ⟨i.val,(Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩
  let L (i : Fin (m.val+1)) := f (jet(z,idx i))
  let coeff (i : Fin (m.val+1)) : ℂ := (m.val.choose i.val:ℂ)*t (m.val-i.val)
  have hφ : Continuous φ.val := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have ht (q : ℕ) : ‖t q‖ ≤ q.factorial*M/(2*R)^q := by
    rw [show t q = _ from translate_mellin_zero (χ z.val.1) φ w₀ q]
    apply radialMoment_cauchy μ𝔽 logNorm (fun g : C𝔽 ↦ φ.val g * (χ z.val.1 g:ℂ)) (continuous_logModule' (G := C𝔽) m𝔽)
      (hφ.mul (continuous_subtype_val.comp (χ z.val.1).continuous))
      (show HasCompactSupport φ.val from φ.property.2).mul_right _ _ (by dsimp [R]; positivity)
    intro w hw
    have h := translate_mellin_zero (χ z.val.1) φ w 0
    simp only [pow_zero,mul_one] at h
    exact (congrArg norm h.symm).le.trans (hfreq w hw)
  have hL : (f (jet(z,m))).comp (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ) =
      ∑ i : Fin (m.val+1), coeff i • L i := by
    ext u
    simp only [sum_apply,ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul]
    exact allMoments_action a hα hs χ f hj φ z m u
  rw [hL]
  apply (norm_sum_le Finset.univ (fun i : Fin (m.val+1) ↦ coeff i • L i)).trans
  calc
    _ ≤ ∑ i : Fin (m.val+1), (1/2:ℝ)^(m.val-i.val) * (2*M*‖f (jet(z,m))‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [allMoments_norm_smul]
      change ‖(m.val.choose i.val:ℂ)*t (m.val-i.val)‖ * ‖L i‖ ≤ _
      rw [norm_mul,Complex.norm_natCast]
      exact allMoments_scaled _ (Real.exp_pos _) hM (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (norm_nonneg (L i)) (norm_nonneg (f (jet(z,m))))
        (allMoments_ratio a hα hs χ f hj z m (idx i) (Nat.le_of_lt_succ i.isLt)) (ht _)
    _ = (∑ i : Fin (m.val+1), (1/2:ℝ)^(m.val-i.val)) * (2*M*‖f (jet(z,m))‖) := (Finset.sum_mul ..).symm
    _ ≤ 2*(2*M*‖f (jet(z,m))‖) := mul_le_mul_of_nonneg_right (allMoments_geometric _) (by positivity)
    _ = _ := by ring
#print axioms allMoments_composed_norm
private theorem stripRectangles_of_summable_coordinate_conditioning
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a,hStrip(hα),hs₀(hs))) (f : J(χ) → StrongDual ℂ Q(a,hStrip(hα),hs₀(hs)))
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ,j)))
    (φ : BruhatCompactSupport C𝔽) (M : Z(χ,α) → ℝ) (hM : ∀ z, 0 ≤ M z)
    (hfreq : ∀ z : Z(χ,α), ∀ w ∈ Metric.sphere (shift(z.val.2.1,z.val.2.2)) (2*Real.exp ((4*α+s)/2)),
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖ ≤ M z)
    (hcoord : Summable (fun z : Z(χ,α) ↦ M z *
      ∑ m : Fin (N(χ,α,s,z)), ‖f (jet(z,m))‖ * ‖x (jet(z,m))‖))
    (e : Z(χ,α) ↪ ℕ × ℕ) :
    SpectralRectanglesTraceCauchy (fun i ↦ spectralConvolutionFiniteSum
      (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ) x f
      (((Finset.Iic i.1).product (Finset.Iic i.2)).preimage e e.injective.injOn)
      (fun z : Z(χ,α) ↦ N(χ,α,s,z)) (fun z m ↦ jet(z,m))) := by
  apply rectangles_of_rankOne_majorant _ _ _ _ _ e _ (hcoord.mul_left 4)
  intro z
  change _ ≤ 4*(M z * ∑ m : Fin (N(χ,α,s,z)), ‖f (jet(z,m))‖ * ‖x (jet(z,m))‖)
  rw [←mul_assoc,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right (allMoments_composed_norm a hα hs χ f hj φ z m _ (hM z) (hfreq z)) (norm_nonneg _)
#print axioms stripRectangles_of_summable_coordinate_conditioning
private theorem allMoments_polynomial_atom {H C K v u t : ℝ} (d p : ℕ)
    (hH : 0 < H) (hK : 0 ≤ K) (hu : 0 ≤ u)
    (ht : t ≤ 4*(K/H^(d+p))*v) (hcond : v*u ≤ C*H^d) :
    t*u ≤ (4*K*C)/H^p := by
  have hpos : 0 ≤ 4*(K/H^(d+p)) := by positivity
  calc
    _ ≤ (4*(K/H^(d+p)))*(v*u) := (mul_le_mul_of_nonneg_right ht hu).trans_eq (mul_assoc ..)
    _ ≤ (4*(K/H^(d+p)))*(C*H^d) := mul_le_mul_of_nonneg_left hcond hpos
    _ = _ := by rw [pow_add]; field_simp

private theorem stripRectangles_of_polynomial_coordinate_conditioning
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a,hStrip(hα),hs₀(hs))) (f : J(χ) → StrongDual ℂ Q(a,hStrip(hα),hs₀(hs)))
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ,j)))
    (φ : BruhatCompactSupport C𝔽) (H : Z(χ,α) → ℝ) (hH : ∀ z, 0 < H z)
    (d p : ℕ) (C K : ℝ) (hK : 0 ≤ K)
    (hcount : Summable (fun z : Z(χ,α) ↦ (N(χ,α,s,z):ℝ)/(H z)^p))
    (hcond : ∀ z : Z(χ,α), ∀ m : Fin (N(χ,α,s,z)),
      ‖f (jet(z,m))‖ * ‖x (jet(z,m))‖ ≤ C*(H z)^d)
    (hfreq : ∀ z : Z(χ,α), ∀ w ∈ Metric.sphere (shift(z.val.2.1,z.val.2.2)) (2*Real.exp ((4*α+s)/2)),
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖ ≤ K/(H z)^(d+p))
    (e : Z(χ,α) ↪ ℕ × ℕ) :
    SpectralRectanglesTraceCauchy (fun i ↦ spectralConvolutionFiniteSum
      (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ) x f
      (((Finset.Iic i.1).product (Finset.Iic i.2)).preimage e e.injective.injOn)
      (fun z : Z(χ,α) ↦ N(χ,α,s,z)) (fun z m ↦ jet(z,m))) := by
  apply rectangles_of_rankOne_majorant _ _ _ _ _ e
    (fun z ↦ (4*K*C)*((N(χ,α,s,z):ℝ)/(H z)^p)) (hcount.mul_left _)
  intro z
  calc
    _ ≤ ∑ _m : Fin (N(χ,α,s,z)), (4*K*C)/(H z)^p := by
      apply Finset.sum_le_sum
      intro m _
      apply allMoments_polynomial_atom d p (hH z) hK (norm_nonneg _)
      · exact allMoments_composed_norm a hα hs χ f hj φ z m _
          (div_nonneg hK (pow_nonneg (hH z).le _)) (hfreq z)
      · exact hcond z m
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
#print axioms stripRectangles_of_polynomial_coordinate_conditioning
end RiemannMasullo

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
  logInfo m!"{n}: {visited.size} reached declarations across {mods.size} modules; zero direct sorryAx dependencies; kernel axioms {axioms}"


run_cmd do
  for n in [``RiemannMasullo.allMoments_composed_norm,
      ``RiemannMasullo.stripRectangles_of_summable_coordinate_conditioning,
      ``RiemannMasullo.stripRectangles_of_polynomial_coordinate_conditioning] do
    auditRoot n
