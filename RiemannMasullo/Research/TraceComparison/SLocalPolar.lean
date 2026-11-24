module

public import Mathlib.LinearAlgebra.Trace
public import RiemannMasullo.Ch12_TraceGeometric.Sec4
public import RiemannMasullo.Research.TraceComparison.SLocalQuotient

/-! # Global Mellin coefficients of the S-local polar moments

The scalar dilation on additive S-adelic tests acts diagonally on the two polar
coordinates in §12.4. The quotient and its measure supply the volume conversion
to the global Mellin integrals in (12.5.1.3). -/

@[expose] public noncomputable section

open IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "mF" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "vF" => (normOneIdeleClassTamagawaMeasure F) univ
local notation "vS" => (sLocalNormOneQuotientMeasure F S) univ
local notation "M(" φ "," s ")" => modulatedFourierMellin mF univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  (ideleClassTamagawaMeasure F) φ (ideleClassNormTwist 1 s)

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1

local instance : T2Space Iₛ := (sIdeleGroup_description F S).2.1

/-- Paper: (12.4.1.4)–(12.4.1.7) and (12.5.1.3), pp. 515–516, 519–520.
For each compact S-idelic lift of the global test, the normalized scalar dilation acts
on evaluation at zero and on the additive integral by the global polar Mellin values
at exponents −1/2 and +1/2, after conversion by the norm-one volumes.
Deviation: The result acts on the two moments of additive Schwartz–Bruhat tests.
The cutoff Paley–Wiener trace and the global strip diagonal require a separate
comparison. -/
theorem sLocalTraceLift_global_polar_moments
    (hPic : Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (hout : ∀ (u : outsideIntegralIdeleUnits F S) (x : C𝔽),
      φ.val (QuotientGroup.mk u.val * x) = φ.val x)
    (f : BruhatCompactSupport Iₛ) (hLift : ∀ g : Iₛ,
      HasSum (fun ξ : sProjectedDiagonal F S ↦ f.val (ξ.val * g))
        (φ.val (QuotientGroup.mk (sIdeleInsertion F S g))))
    (b : SchwartzBruhat (Multiplicative Aₛ)) :
    let k := sLocalTraceDilationKernel f (fun x ↦ b (Multiplicative.ofAdd x))
    ((vF / vS).toReal • k 0, (vF / vS).toReal • ∫ x, k x ∂νₛ) =
      (M(φ.val, -(1 / 2)) * b (Multiplicative.ofAdd 0),
       M(φ.val, 1 / 2) * sAdeleSchwartzFourier b (Multiplicative.ofAdd 0)) := by
  have hpow (g : Iₛ) : (((sIdeleNorm F S g).val : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      (Real.sqrt ((sIdeleNorm F S g).val : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    norm_num
  have hplus := sLocalTraceLift_global_normPowerMellin hPic φ hout f hLift (1 / 2)
  have hminus := sLocalTraceLift_global_normPowerMellin hPic φ hout f hLift (-(1 / 2))
  simp only [hpow] at hplus
  simp only [Complex.cpow_neg, hpow, ← div_eq_mul_inv] at hminus
  obtain ⟨hc, hi⟩ := sLocalTraceTest_continuous_integrable b
  have h := (sLocalTraceDilationKernel_polar_moments f _ hc hi).2
  dsimp only
  rw [sAdeleSchwartzFourier_apply_zero, hplus, hminus, smul_mul_assoc, smul_mul_assoc]
  exact Prod.ext (congrArg ((vF / vS).toReal • ·) (congrArg Prod.fst h))
    (congrArg ((vF / vS).toReal • ·) (congrArg Prod.snd h))

/-- Paper: (12.5.1.3), pp. 519–520. The induced endomorphism of the two-dimensional
space of polar moments is unique, and its trace is the sum of the two global polar
Mellin values. Every pair occurs already on the additive Paley–Wiener test space
with unrestricted Fourier region. The normalization is the same as in the preceding
moment identity. -/
theorem sLocalTraceLift_global_polar_trace
    (hPic : Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (hout : ∀ (u : outsideIntegralIdeleUnits F S) (x : C𝔽),
      φ.val (QuotientGroup.mk u.val * x) = φ.val x)
    (f : BruhatCompactSupport Iₛ) (hLift : ∀ g : Iₛ,
      HasSum (fun ξ : sProjectedDiagonal F S ↦ f.val (ξ.val * g))
        (φ.val (QuotientGroup.mk (sIdeleInsertion F S g)))) :
    ∃! A : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ),
      (∀ b : SchwartzBruhat (Multiplicative Aₛ),
        let k := sLocalTraceDilationKernel f (fun x ↦ b (Multiplicative.ofAdd x))
        A (b (Multiplicative.ofAdd 0), sAdeleSchwartzFourier b (Multiplicative.ofAdd 0)) =
          ((vF / vS).toReal • k 0, (vF / vS).toReal • ∫ x, k x ∂νₛ)) ∧
      LinearMap.trace ℂ (ℂ × ℂ) A = M(φ.val, 1 / 2) + M(φ.val, -(1 / 2)) := by
  let A := LinearMap.prodMap (M(φ.val, -(1 / 2)) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
    (M(φ.val, 1 / 2) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
  have hA (b : SchwartzBruhat (Multiplicative Aₛ)) :=
    (sLocalTraceLift_global_polar_moments hPic φ hout f hLift b).symm
  refine ⟨A, ⟨hA, ?_⟩, ?_⟩
  · simp [A, LinearMap.trace_prodMap', LinearMap.trace_id, add_comm]
  · rintro B ⟨hB, -⟩
    apply LinearMap.ext
    rintro ⟨x, y⟩
    obtain ⟨b, -, hx, hy⟩ := sLocalPWTests_moments_surjective (F := F) (S := S) (T := S)
      Subset.rfl univ Filter.univ_mem x y
    rw [← hx, ← hy]
    exact (hB b).trans (hA b).symm

end RiemannMasullo
