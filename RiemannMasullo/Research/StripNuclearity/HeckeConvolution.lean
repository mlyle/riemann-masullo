module
public import RiemannMasullo.Research.StripNuclearity.Smoothing
public import RiemannMasullo.Research.StripNuclearity.HeckeComponent

/-!
# Smooth compact convolutions after a single Hecke spectral projection
-/

@[expose] public noncomputable section
open Function MeasureTheory NumberField Set
open scoped Topology ContDiff Convolution ComplexConjugate NumberField.AdeleRing

namespace RiemannMasullo.StripNuclearity

private def reflectConj (k : ℝ → ℂ) (x : ℝ) := conj (k (-x))

private theorem reflectConj_contDiff {k : ℝ → ℂ} (hk : ContDiff ℝ (∞) k) :
    ContDiff ℝ (∞) (reflectConj k) := Complex.conjCLE.contDiff.comp (hk.comp contDiff_neg)

private theorem reflectConj_compact {k : ℝ → ℂ} (hk : HasCompactSupport k) :
    HasCompactSupport (reflectConj k) := by
  have h : HasCompactSupport (fun x : ℝ ↦ k (-x)) := hk.comp_homeomorph (Homeomorph.neg ℝ)
  exact h.comp_left (show conj (0 : ℂ) = 0 from map_zero _)

private theorem reflectConj_involution (k : ℝ → ℂ) : reflectConj (reflectConj k) = k := by
  funext x
  simp [reflectConj]

private theorem scalar_convolution_operators {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (k : ℝ → ℂ) (hk : HasCompactSupport k) (hkc : ContDiff ℝ (∞) k) :
    let θ := intervalSobolevDensity (-α) α s
    let E := CompactIntervalSobolev volume id (-α) α s
    ∃ B : E →L[ℂ] E, HasWeightedAdjointKernel θ k B := by
  intro θ E
  have hw : Continuous θ := by
    unfold θ intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun x ↦ Or.inl ?_)
    positivity
  have hp (x : ℝ) : 0 < θ x := mul_pos (lt_max_of_lt_left (Real.exp_pos _))
    (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨A,hA⟩ := exists_scalar_weighted_convolution (-α) α s (by linarith) hs
    (reflectConj k) (reflectConj_contDiff hkc).continuous (reflectConj_compact hk)
  refine ⟨A.adjoint,?_⟩
  intro u g hgc hgs hu
  have he := weighted_convolution_adjoint_compact hw hp (reflectConj k) (reflectConj_contDiff hkc).continuous
    (reflectConj_compact hk) A (fun v ↦ (hA v).mono fun _ h ↦ h.2) u g hgc hgs hu
  simpa only [show (fun t ↦ conj (reflectConj k (-t))) = k from reflectConj_involution k] using he

/-- For any fixed unitary Hecke character and closed strip centered at one-half,
all smooth compactly supported radial convolution operators are trace class
after projection onto the admitted Mellin jet space. No zero spacing or
rectangular basis convergence is assumed. -/
theorem exists_projected_hecke_convolution {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {α s : ℝ} (ha : 0 ≤ α) (hs : 1 < s) :
    let D := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
    let Z := {z : ℂ // 0 < D z ∧ |z.re - 1/2| ≤ α}
    let w := fun z : Z ↦ (⟨z.val.re - 1/2, z.val.im⟩ : ℂ)
    let m := fun z : Z ↦ spectralStripMultiplicity α s (w z).re (D z.val).toNat
    let d := α+s+2
    let E := CompactIntervalSobolev volume id (-α) α s
    let I := Ioo (-d) d
    let J := Σ z, Fin (m z)
    ∃ (j : PositiveRealExponentialDecay I →L[ℂ] E) (Λ : J → StrongDual ℂ E),
      DenseRange j ∧ (∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) ∧
      (∀ (l : J) p, Λ l (j p) = iteratedDeriv l.2.val
        (mellin (fun t ↦ p.val (Real.log t))) (w l.1)) ∧
      ∀ (κ : ℝ → ℂ), HasCompactSupport κ → ContDiff ℝ (∞) κ →
        ∀ A : E →L[ℂ] E, (∀ f, ∀ᵐ x ∂volume, A f x = ∫ t : ℝ, κ t * f (x-t)) →
          IsNuclearOperator (A.comp ((⨅ l, (Λ l).ker).orthogonal.starProjection)) := by
  intro D Z w m d E I J
  obtain ⟨j,R,Λ,hdense,hj,hR,hΛ,hN⟩ := exists_projected_hecke_resolvent χ ha hs
  refine ⟨j,Λ,hdense,hj,hΛ,?_⟩
  intro κ hk hsκ A hA
  let θ := intervalSobolevDensity (-α) α s
  have hw : Continuous θ := by
    unfold θ intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun x ↦ Or.inl ?_)
    positivity
  have hp (x : ℝ) : 0 < θ x := mul_pos (lt_max_of_lt_left (Real.exp_pos _))
    (Real.rpow_pos_of_pos (by positivity) _)
  let k := reflectConj κ
  have hks := reflectConj_compact hk
  have hkd := reflectConj_contDiff hsκ
  have hk' := (contDiff_infty_iff_deriv.mp hkd).2
  have hk'' := (contDiff_infty_iff_deriv.mp hk').2
  have hB : HasWeightedAdjointKernel θ k A.adjoint :=
    weighted_convolution_adjoint_compact hw hp κ hsκ.continuous hk A hA
  obtain ⟨B₁,hB₁⟩ := scalar_convolution_operators ha (le_of_lt (by linarith : 0 < s))
    (deriv k) hks.deriv hk'
  obtain ⟨B₂,hB₂⟩ := scalar_convolution_operators ha (le_of_lt (by linarith : 0 < s))
    (deriv (deriv k)) hks.deriv.deriv hk''
  have hd : 0 < d := by dsimp [d]; linarith
  have hn (z : ℂ) (hz : z.re ∈ I) : (((d+1 : ℝ) : ℂ)^2-z^2) ≠ 0 := by
    have hx := (sq_le_sq₀ (abs_nonneg z.re) hd.le).mpr (abs_le.mpr ⟨hz.1.le,hz.2.le⟩)
    rw [sq_abs] at hx
    have hpos : 0 < (((d+1 : ℝ) : ℂ)^2-z^2).re := by
      simp [sq,Complex.mul_re]
      nlinarith [sq_nonneg z.im]
    exact fun hx ↦ (ne_of_gt hpos) (congrArg Complex.re hx)
  have h := nuclear_weighted_convolution_of_projected_resolvent ha isOpen_Ioo ordConnected_Ioo
    ⟨0,(show -(d:ℝ) < 0 by linarith),hd⟩ (d+1) hn k hks hkd
    j R _ A.adjoint B₁ B₂ hj hR hN hB hB₁ hB₂
  simpa only [ContinuousLinearMap.adjoint_adjoint] using h

end RiemannMasullo.StripNuclearity
