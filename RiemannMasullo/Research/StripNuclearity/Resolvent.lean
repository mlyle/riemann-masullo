module

public import RiemannMasullo.Research.StripNuclearity.FiniteCutoffs
public import RiemannMasullo.Research.StripNuclearity.HeightCount
public import RiemannMasullo.Research.StripNuclearity.HeightTails
public import RiemannMasullo.Research.StripNuclearity.ScalarAction

/-!
# Trace-class resolvents on a scalar Mellin-jet component

Quadratic summability of the prescribed zero multiplicities suffices for a
single resolvent on the radial spectral component. All dimensions count full
multiplicities. No bounds on the norms of coordinate projections are needed.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Real Set
open scoped Topology

namespace RiemannMasullo.StripNuclearity

private theorem height_windows {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hs : Summable fun i ↦ (m i : ℝ) / (1+|(a i).im|)^2) :
    ∃ S : ℕ → Finset ι, (∀ n i, i ∈ S n ↔ |(a i).im| ≤ (2 : ℝ)^n) ∧
      let K := fun n ↦ (S n).sigma fun i ↦ (Finset.univ : Finset (Fin (m i)))
      Summable fun n : ℕ ↦ ((K (n+1)).card : ℝ) * (1/4 : ℝ)^n := by
  classical
  let t (i : ι) := |(a i).im|
  have hf (n : ℕ) : {i : ι | t i ≤ (2 : ℝ)^n}.Finite := by
    let ε := 1 / (1 + (2 : ℝ)^n)^2
    have he : 0 < ε := by dsimp [ε]; positivity
    have hl : ∀ᶠ i in cofinite, (m i : ℝ) / (1+t i)^2 < ε :=
      hs.tendsto_cofinite_zero.eventually_lt (tendsto_const_nhds (x := ε)) he
    apply (eventually_cofinite.mp hl).subset
    intro i hi
    change t i ≤ _ at hi
    change ¬ _ < _
    apply not_lt_of_ge
    apply div_le_div₀ (by norm_num) (by exact_mod_cast hm i) (by dsimp [t]; positivity)
    exact pow_le_pow_left₀ (by dsimp [t]; positivity) (by linarith) 2
  let S (n : ℕ) := (hf n).toFinset
  have hS (n : ℕ) (i : ι) : i ∈ S n ↔ t i ≤ 2^n := Set.Finite.mem_toFinset _
  refine ⟨S, hS, ?_⟩
  intro K
  let H (j : Σ i, Fin (m i)) := 1+t j.1
  have hpos (j) : 0 < H j := by dsimp [H,t]; positivity
  have hσ : Summable fun j ↦ (H j ^2)⁻¹ := by
    apply (summable_sigma_of_nonneg (fun j ↦ inv_nonneg.mpr (sq_nonneg (H j)))).mpr
    refine ⟨fun _ ↦ Summable.of_finite, ?_⟩
    convert hs using 1
    funext i
    simp [H,t, div_eq_mul_inv]
  apply summable_dyadic_card_of_quadratic_heights H hpos hσ 3 (by norm_num) (fun n ↦ K (n+1))
  intro n i hi
  have hh := (hS _ i.1).mp (Finset.mem_sigma.mp hi).1
  rw [pow_succ] at hh
  dsimp [H]
  linarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := n)]

private theorem vanishing_profile_jet {I : Set ℝ} (hI : IsOpen I) (hi : OrdConnected I)
    {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b (Complex.re ⁻¹' I))
    (p q : PositiveRealExponentialDecay I)
    (h : ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
      b z * mellin (fun t ↦ p.val (Real.log t)) z)
    {z : ℂ} (hz : z.re ∈ I) {m k : ℕ}
    (hm : (m : ℕ∞) ≤ analyticOrderAt b z) (hk : k < m) :
    iteratedDeriv k (mellin (fun t ↦ q.val (Real.log t))) z = 0 := by
  let M := positiveRealFourierMellin I hI hi ⟨z.re,hz⟩
  let H := M p
  have hopen := hI.preimage Complex.continuous_re
  have ha := hb.analyticAt (hopen.mem_nhds hz)
  have hH : AnalyticAt ℂ H.val z := H.property.2.1.analyticAt (hopen.mem_nhds hz)
  have he : mellin (fun t ↦ q.val (Real.log t)) =ᶠ[𝓝 z] fun w ↦ b w * H.val w := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact (h w hw).trans (congrArg (b w * ·) (positiveRealFourierMellin_apply I hI hi _ p w hw).symm)
  rw [he.iteratedDeriv_eq]
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (ha.mul hH)).mp _ k hk
  change (m : ℕ∞) ≤ analyticOrderAt (fun w ↦ b w * H.val w) z
  rw [analyticOrderAt_fun_mul ha hH]
  exact hm.trans le_self_add



/-- A single second-order radial resolvent, restricted by the orthogonal
projection onto a total family of Mellin jets, is trace class after taking
its adjoint. The zero count enters with the full quadratic exponent. -/
theorem exists_projected_scalar_resolvent {ι : Type*} (w : ι → ℂ) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hsum : Summable fun i ↦ (m i : ℝ) / (1+|(w i).im|)^2)
    {α s d β A k : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) (hβ : 2*α+s < 2*β) (hd : β < d)
    (hk : 0 < k) (hwidth : k * (d+|A|) < π/2)
    (hw : ∀ i, |(w i).re| < d) (h0 : ∀ i, stripBlaschkeToDisk (A : ℂ) k (w i) ≠ 0) :
    let E := CompactIntervalSobolev volume id (-α) α s
    let I := Ioo (-d) d
    let J := Σ i, Fin (m i)
    let r := fun z : ℂ ↦ ((((d+1 : ℝ) : ℂ)^2 - z^2)⁻¹)
    ∃ (j : PositiveRealExponentialDecay I →L[ℂ] E) (R : E →L[ℂ] E),
      DenseRange j ∧ (∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) ∧
      (∀ p, ∃ q : PositiveRealExponentialDecay I, R (j p) = j q ∧
        ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
          r z * mellin (fun t ↦ p.val (Real.log t)) z) ∧
      ∀ (P : E →L[ℂ] E), IsSelfAdjoint P → ∀ Λ : J → StrongDual ℂ E,
        (∀ x ∈ P.toLinearMap.range, (∀ l, Λ l x = 0) → x = 0) →
        (∀ l x, Λ l (P x) = Λ l x) →
        (∀ (l : J) p, Λ l (j p) = iteratedDeriv l.2.val
          (mellin (fun t ↦ p.val (Real.log t))) (w l.1)) →
        IsNuclearOperator (R.adjoint.comp P) := by
  classical
  intro E I J r
  have hd0 : 0 < d := by linarith
  have hI0 : 0 ∈ I := ⟨by linarith,hd0⟩
  have hIβ : β ∈ I := ⟨by linarith,hd⟩
  have hIβ' : -β ∈ I := ⟨by linarith,by linarith⟩
  have hemb : Icc (-α) α ⊆ I := fun x ⟨h₁,h₂⟩ ↦ ⟨by linarith,by linarith⟩
  have hgap (z : ℂ) (hz : |z.re| ≤ d) : 0 < (((d+1 : ℝ) : ℂ)^2-z^2).re := by
    have hx := (sq_le_sq₀ (abs_nonneg _) hd0.le).mpr hz
    rw [sq_abs] at hx
    simp [sq, Complex.mul_re]
    nlinarith [sq_nonneg z.im]
  have hIabs (z : ℂ) (hz : z.re ∈ I) : |z.re| ≤ d := abs_le.mpr ⟨hz.1.le,hz.2.le⟩
  have hr : ContractiveStripSymbol I r := by
    constructor
    · apply DifferentiableOn.inv
      · exact (differentiableOn_const _).sub (differentiableOn_id.pow 2)
      · intro z hz h
        have hh := congrArg Complex.re h
        exact (ne_of_gt (hgap z (hIabs z hz))) hh
    · intro z hz
      apply (resolvent_norm_le hd0.le (lt_add_one d) z (hIabs z hz)).trans
      have : 1 ≤ (d+1)^2-d^2+z.im^2 := by nlinarith [sq_nonneg z.im]
      simpa using (inv_anti₀ (by norm_num : (0:ℝ) < 1) this)
  let qR : {f : ℂ → ℂ // ContractiveStripSymbol I f} := ⟨r,hr⟩
  obtain ⟨j,U,C,hC,hdense,hj,-,hact,hop⟩ := exists_scalar_multiplier_action
    isOpen_Ioo ordConnected_Ioo hI0 ha hs hβ hIβ hIβ' hemb
  refine ⟨j,U qR,hdense,hj,hact qR,?_⟩
  intro P hP Λ hsep hΛP hjet
  obtain ⟨S,hS,hcards⟩ := height_windows w m hm hsum
  let K (n : ℕ) := (S n).sigma fun i ↦ (Finset.univ : Finset (Fin (m i)))
  have hK (n : ℕ) (l : J) : l ∈ K n ↔ |(w l.1).im| ≤ (2:ℝ)^n := by
    change l ∈ (S n).sigma _ ↔ _
    rw [Finset.mem_sigma, hS]; simp
  have hmono : Monotone K := fun n n' hn l hl ↦ (hK n' l).mpr
    (((hK n l).mp hl).trans (pow_right_mono₀ (by norm_num) hn))
  have hmargin (z : ℂ) (hz : |z.re| ≤ d) : |z.re-A| ≤ d+|A| :=
    (abs_sub _ _).trans (add_le_add_left hz _)
  have hall (z : ℂ) (hz : |z.re| ≤ d) : |z.re-A| < (π/2)/k :=
    (hmargin z hz).trans_lt ((lt_div_iff₀ hk).mpr (by linarith))
  obtain ⟨B,M,hM,hb,hbound,hord,hsmall⟩ := exists_quantitative_strip_tails w m A k
    (d+|A|) hk (add_nonneg hd0.le (abs_nonneg _)) hwidth (fun i ↦ hall _ (hw i).le) h0 hsum
  let b (n : ℕ) : {f : ℂ → ℂ // ContractiveStripSymbol I f} :=
    ⟨B (S n), (hb (S n)).differentiableOn.mono (fun z hz ↦ hall z (hIabs z hz)),
      fun z hz ↦ hbound _ _ (hall z (hIabs z hz))⟩
  have hv (n : ℕ) (l : J) (hl : l ∉ K n) (x : E) : Λ l (P ((U (b n)) x)) = 0 := by
    rw [hΛP]
    suffices h : (Λ l).comp (U (b n)) = 0 from congrArg (fun f : E →L[ℂ] ℂ ↦ f x) h
    apply DFunLike.coe_injective
    apply hdense.equalizer ((Λ l).comp (U (b n))).continuous (0 : StrongDual ℂ E).continuous
    funext p
    obtain ⟨q,hq,hbq⟩ := hact (b n) p
    change Λ l (U (b n) (j p)) = 0
    rw [hq, hjet]
    have hz : (w l.1).re ∈ I := abs_lt.mp (hw l.1)
    apply vanishing_profile_jet isOpen_Ioo ordConnected_Ioo (b n).property.1 p q hbq hz _ l.2.isLt
    apply hord
    exact fun hh ↦ hl ((hK n l).mpr ((hS n l.1).mp hh))
  obtain ⟨L,hL,hnum⟩ := cutoff_resolvent_norm_le hd0.le (lt_add_one d) (by positivity : 0 < k/4) hM
  have hboundOp (n : ℕ) :
      ‖(U (b n) - ContinuousLinearMap.id ℂ E).comp (U qR)‖ ≤ (C * (L+1)) * (1/4 : ℝ)^n := by
    let T := (2 : ℝ)^n
    have hT : 0 < T := by dsimp [T]; positivity
    have hsml (z : ℂ) (hz : |z.re| ≤ d) (ht : |z.im| ≤ T/2) :
        ‖(b n).val z - 1‖ ≤ M * exp (-(k/4)*T) :=
      hsmall _ T (fun i hi ↦ le_of_not_ge (fun hh ↦ hi ((hS n i).mpr hh))) z (hmargin z hz) ht
    have hnum' := hnum T hT (b n).val (fun z hz ↦ hbound _ z (hall z hz)) hsml
    have hh := hop (b n) qR ((L+1)/T^2) (by positivity) (fun z hz ↦
      (hnum' z (hIabs z hz)).trans (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)))
    have hdy : (1/4 : ℝ)^n = (T^2)⁻¹ := by
      dsimp [T]; rw [← pow_mul, Nat.mul_comm, pow_mul, ← inv_pow]; norm_num
    rw [hdy]
    simpa only [div_eq_mul_inv, mul_assoc] using hh
  have hgeom := summable_geometric_of_lt_one (by norm_num : 0 ≤ (1/4 : ℝ)) (by norm_num : (1/4 : ℝ) < 1)
  apply nuclear_comp_projection_of_moment_cutoffs (U qR).adjoint P hP Λ hsep (fun n ↦ U (b n)) K hmono hv
  simp only [ContinuousLinearMap.adjoint_adjoint]
  refine ((hcards.add hgeom).mul_left (C*(L+1))).of_nonneg_of_le (fun n ↦ by positivity) ?_
  intro n
  calc
    _ ≤ (((K (n+1)).card : ℝ) + 1) * ((C * (L+1)) * (1/4 : ℝ)^n) :=
      mul_le_mul_of_nonneg_left (hboundOp n) (by positivity)
    _ = _ := by dsimp [K]; ring

end RiemannMasullo.StripNuclearity
