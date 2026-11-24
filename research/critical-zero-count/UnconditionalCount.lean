module
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RiemannMasullo.External.ZetaLab.Zeta23.Statement.SeamClosed
import RiemannMasullo.External.ZetaLab.Zeta23.Hypotheses
import Zeta23.Final
import Mathlib.Tactic

@[expose] public noncomputable section
open Set Real
namespace RiemannMasullo

/-- Dyadic asymptotics and a positive fraction of distinct critical-line
zeros imply arbitrarily large linear excesses in the dyadic windows. -/
private theorem spectralLineJet_dyadic_linear_excess
    (N D : ℝ → ℕ)
    (hRvM : ∃ C T₀ : ℝ, ∀ T, T₀ ≤ T →
      |(N T : ℝ) - T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) + 2 * Real.log 2 - 1)| ≤
        C * Real.log T)
    (hD : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (N T : ℝ) ≤ (D T : ℝ)) (k : ℕ) :
    ∃ T : ℕ, 0 < T ∧ (k + 1) * (2 * T + 1) < D T := by
  obtain ⟨C, T₀, hM⟩ := hRvM
  obtain ⟨T₁, hprop⟩ := hD (1 / 6 : ℝ) (by norm_num)
  let A : ℝ := 8 * ((k : ℝ) + 1) + |C| + 1
  have hπ : 0 < 2 * Real.pi := by positivity
  obtain ⟨T, hT⟩ := exists_nat_gt (max (max T₀ T₁) (max 1
    ((2 * Real.pi) * Real.exp (2 * Real.pi * A + 1))))
  have hT₀ := ((le_max_left T₀ T₁).trans (le_max_left _ _)).trans hT.le
  have hT₁ := ((le_max_right T₀ T₁).trans (le_max_left _ _)).trans hT.le
  have hT1 : (1 : ℝ) ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT.le
  have hT0 : (0 : ℝ) < T := zero_lt_one.trans_le hT1
  have hbig := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hT
  have hlog : 2 * Real.pi * A + 1 < Real.log ((T : ℝ) / (2 * Real.pi)) := by
    apply (Real.lt_log_iff_exp_lt (div_pos hT0 hπ)).mpr
    exact (lt_div_iff₀ hπ).mpr (by simpa only [mul_comm] using hbig)
  have hcoeff : A < (Real.log ((T : ℝ) / (2 * Real.pi)) + 2 * Real.log 2 - 1) / (2 * Real.pi) :=
    (lt_div_iff₀ hπ).mpr (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
  have hmain := mul_lt_mul_of_pos_left hcoeff hT0
  have herr : C * Real.log T ≤ |C| * T :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.log_nonneg hT1)).trans
      (mul_le_mul_of_nonneg_left (Real.log_le_self hT0.le) (abs_nonneg C))
  have hr := (abs_le.mp (hM T hT₀)).1
  have hp := hprop T hT₁
  have hN : (T : ℝ) * (8 * ((k : ℝ) + 1) + 1) < (N T : ℝ) := by
    unfold A at hmain
    have hprod (v : ℝ) : (T : ℝ) / (2 * Real.pi) * v = T * (v / (2 * Real.pi)) := by ring
    rw [hprod] at hr
    linarith [show (T : ℝ) * (8 * ((k : ℝ) + 1) + |C| + 1) =
      T * (8 * ((k : ℝ) + 1) + 1) + |C| * T by ring]
  refine ⟨T, by exact_mod_cast hT0, ?_⟩
  have hn : ((k : ℝ) + 1) * (2 * (T : ℝ) + 1) < (D T : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hT1 (by positivity : 0 ≤ (k : ℝ) + 1)]
  exact_mod_cast hn

/-- On a vertical line, projecting to ordinates preserves cardinality. -/
private theorem spectralLineJet_ordinates_of_dyadic_excess
    (Z : ℝ → Set ℂ) (hf : ∀ T, (Z T).Finite)
    (hz : ∀ T z, z ∈ Z T → riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ T < z.im ∧ z.im ≤ 2 * T)
    (hcount : ∀ k : ℕ, ∃ T : ℕ, 0 < T ∧ (k + 1) * (2 * T + 1) < (Z T).ncard)
    (k : ℕ) : ∃ T : ℕ, ∃ S : Finset ℝ, (k + 1) * (T + 1) < S.card ∧
      ∀ t ∈ S, t ∈ Ioc (0 : ℝ) T ∧ riemannZeta (1/2 + (t : ℂ) * Complex.I) = 0 := by
  classical
  obtain ⟨T, hT, hsize⟩ := hcount k
  let S := (hf T).toFinset
  refine ⟨2 * T, S.image Complex.im, ?_, ?_⟩
  · have hinj : Set.InjOn Complex.im S := by
      intro x hx y hy h
      exact Complex.ext ((hz T x ((hf T).mem_toFinset.mp hx)).2.1.trans
        (hz T y ((hf T).mem_toFinset.mp hy)).2.1.symm) h
    rw [Finset.card_image_of_injOn hinj]
    simpa only [Set.ncard_eq_toFinset_card _ (hf T)] using hsize
  · intro t ht
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hzero, hre, hlo, hhi⟩ := hz T z ((hf T).mem_toFinset.mp hzS)
    refine ⟨⟨lt_trans (by exact_mod_cast hT) hlo, by exact_mod_cast hhi⟩, ?_⟩
    have hr : (z.re : ℂ) = 1/2 := by rw [hre]; norm_num
    rwa [← hr, Complex.re_add_im]

/-- The two arithmetical inputs have exactly the types of Zeta23's
`riemannVonMangoldt_zeta` and `thmA₀` at commit 16a5ce4. -/
private theorem spectralLineJet_count_of_zeta23
    (hRvM : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig)
    (hA : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2/3 - ε) * (Zeta23.Ncount T (2*T) : ℝ) ≤ Zeta23.N0star T (2*T))
    (k : ℕ) : ∃ T : ℕ, ∃ S : Finset ℝ, (k + 1) * (T + 1) < S.card ∧
      ∀ t ∈ S, t ∈ Ioc (0 : ℝ) T ∧ riemannZeta (1/2 + (t : ℂ) * Complex.I) = 0 := by
  let Z (T : ℝ) := Zeta23.zerosIn T (2*T) ∩ {z : ℂ | z.re = 1/2}
  apply spectralLineJet_ordinates_of_dyadic_excess Z (fun T ↦ (Zeta23.zerosIn_finite T (2*T)).inter_of_left _) _ _ k
  · intro T z hz
    exact ⟨hz.1.1.1, hz.2, hz.1.2⟩
  · refine spectralLineJet_dyadic_linear_excess (fun T ↦ Zeta23.Ncount T (2*T)) (fun T ↦ (Z T).ncard) ?_ ?_
    · simpa only [Zeta23.zetaZeroConfig_N, Zeta23.ell1, Zeta23.l] using hRvM.main
    · exact hA

theorem verified_critical_zero_count (k : ℕ) :
    ∃ T : ℕ, ∃ S : Finset ℝ, (k + 1) * (T + 1) < S.card ∧
      ∀ t ∈ S, t ∈ Ioc (0 : ℝ) T ∧ riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 :=
  spectralLineJet_count_of_zeta23 Zeta23.riemannVonMangoldt_zeta Zeta23.thmA₀ k
#print axioms verified_critical_zero_count
#print axioms Zeta23.riemannVonMangoldt_zeta
#print axioms Zeta23.thmA₀
end RiemannMasullo
end
