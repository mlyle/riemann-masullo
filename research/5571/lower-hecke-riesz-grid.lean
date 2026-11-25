import RiemannMasullo.Ch13_ZerosHecke.HeckeRieszMellin
import RiemannMasullo.Ch13_ZerosHecke.HeckeRieszZeroDetection

open Complex MeasureTheory NumberField Set Function
open scoped NNReal Classical
namespace RiemannMasullo
variable {K : Type*} [Field K] [NumberField K]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 K) K)

theorem physicalRealHeckeRiesz_iff_critical_line
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1) :
    (∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {z | 1 / 2 < z.re} ∧
      ∀ s : ℂ, 1 < s.re → H s =
        (∫ x in Ioi (1 : ℝ), ((heckeFirstRieszMean χ x).re : ℂ) * (x : ℂ) ^ (-s - 2)) -
          (if χ = 1 then 1 else 0) / (2 * (s - 1))) ↔
    ∀ p : ℂ, 0 < MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ p → p.re = 1 / 2 := by
  classical
  rw [← hecke_centeredRealRieszLogDeriv_iff_critical_line τ hτ χ hχ]
  let L := Classical.choose (finiteHeckeL_exists_continuation χ)
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  have hphysical (s : ℂ) (hs : 1 < s.re) :
      (∫ x in Ioi (1 : ℝ), ((heckeFirstRieszMean χ x).re : ℂ) * (x : ℂ) ^ (-s - 2)) -
        (if χ = 1 then 1 else 0)/(2*(s-1)) =
        centeredRealRieszLogDeriv L (if χ = 1 then 1 else 0) s := by
    rw [heckeFirstRieszMean_re_mellin χ L hL.1 hL.2 hs]
    by_cases hn : χ = 1 <;> simp [centeredRealRieszLogDeriv, hn]
  constructor
  · rintro ⟨H, hH, he⟩
    exact ⟨H, hH, fun s hs ↦ (he s hs).trans (hphysical s hs)⟩
  · rintro ⟨H, hH, he⟩
    exact ⟨H, hH, fun s hs ↦ (he hs).trans (hphysical s hs).symm⟩

#print axioms physicalRealHeckeRiesz_iff_critical_line
end RiemannMasullo
