module

public import RiemannMasullo.ForMathlib.Analysis.Complex.Blaschke
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Division by the zeros of a bounded analytic function

The normalized Blaschke product removes exactly the zeros of a bounded analytic function on
the unit disk. Its holomorphic quotient is zero-free and has the same supremum bound. For
division by a finite product, the maximum principle on concentric disks gives the bound.
Passing to complementary products then gives the corresponding bound for the full divisor.
-/

@[expose] public noncomputable section
open Filter Function MeromorphicOn Metric Set
open scoped Topology

namespace RiemannMasullo.Blaschke

/-- A continuous finite inner multiplier with modulus one on the unit circle
preserves the supremum bound of an analytic function on the open disk. -/
theorem disk_inner_multiplier_bound (P F : ℂ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hP : ContinuousOn P (closedBall 0 1))
    (hboundary : ∀ w ∈ sphere (0 : ℂ) 1, ‖P w‖ = 1)
    (hF : AnalyticOnNhd ℂ F (ball 0 1))
    (hb : ∀ w ∈ ball (0 : ℂ) 1, ‖P w * F w‖ ≤ M) (w : ℂ) (hw : w ∈ ball 0 1) :
    ‖F w‖ ≤ M := by
  by_contra! h
  have hn := hM.trans_lt h
  obtain ⟨m, hm, h1⟩ := exists_between ((div_lt_one hn).mpr h)
  have hmpos := (div_nonneg hM hn.le).trans_lt hm
  let K := {z ∈ closedBall (0 : ℂ) 1 | ‖P z‖ ≤ m}
  have hK : IsClosed K := hP.norm.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic
  have hsub : K ⊆ ball 0 1 := by
    intro z hz
    have hzball : ‖z‖ ≤ 1 := by simpa [mem_closedBall] using hz.1
    refine mem_ball_zero_iff.mpr (lt_of_le_of_ne hzball ?_)
    intro hz'
    have he := hboundary z (by simpa [mem_sphere] using hz')
    have hp := hz.2
    linarith
  obtain ⟨R, hR, hRsub⟩ := exists_lt_subset_ball hK hsub
  obtain ⟨r, hl, hr⟩ := exists_between (max_lt hR (mem_ball_zero_iff.mp hw))
  have hRr := (le_max_left R ‖w‖).trans_lt hl
  have hwr := (le_max_right R ‖w‖).trans_lt hl
  have hc : ‖F w‖ ≤ M / m := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hF.differentiableOn.diffContOnCl_ball (closedBall_subset_ball hr))
    · intro z hz
      have hs := frontier_ball_subset_sphere hz
      have hzr : ‖z‖ = r := by simpa [mem_sphere] using hs
      have hzi := mem_ball_zero_iff.mpr (hzr.trans_lt hr)
      have hzm : m ≤ ‖P z‖ := by
        by_contra! hlt
        have hzK : z ∈ K := ⟨ball_subset_closedBall hzi, hlt.le⟩
        have := mem_ball_zero_iff.mp (hRsub hzK)
        linarith
      have hp := hb z hzi
      rw [norm_mul] at hp
      exact (le_div_iff₀ hmpos).mpr (by nlinarith [mul_le_mul_of_nonneg_right hzm (norm_nonneg (F z))])
    · exact subset_closure (mem_ball_zero_iff.mpr hwr)
  have hlow := (div_lt_iff₀ hn).mp hm
  have hupp := (le_div_iff₀ hmpos).mp hc
  linarith

private theorem exists_analytic_quotient_of_order_le {U : Set ℂ} (f P : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (hP : AnalyticOnNhd ℂ P U)
    (hord : ∀ z ∈ U, ∃ n : ℕ, analyticOrderAt P z = n ∧ ↑n ≤ analyticOrderAt f z) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F U ∧ (∀ z ∈ U, P z * F z = f z) ∧
      ∀ z ∈ U, analyticOrderAt f z = analyticOrderAt P z → F z ≠ 0 := by
  let F := toMeromorphicNFOn (f / P) U
  have hm : MeromorphicOn (f / P) U := hf.meromorphicOn.div hP.meromorphicOn
  have hnormal : MeromorphicNFOn F U := meromorphicNFOn_toMeromorphicNFOn _ _
  have hdiff (z : ℂ) (hz : z ∈ U) :
      meromorphicOrderAt F z = meromorphicOrderAt f z - meromorphicOrderAt P z := by
    change meromorphicOrderAt (toMeromorphicNFOn (f / P) U) z = _
    rw [meromorphicOrderAt_toMeromorphicNFOn hm hz,
      meromorphicOrderAt_div (hf z hz).meromorphicAt (hP z hz).meromorphicAt]
  have horders (z : ℂ) (hz : z ∈ U) : 0 ≤ meromorphicOrderAt F z ∧ meromorphicOrderAt P z ≠ ⊤ := by
    obtain ⟨n, hP₀, hf₀⟩ := hord z hz
    have hp : meromorphicOrderAt P z = ((n : ℤ) : WithTop ℤ) := by rw [(hP z hz).meromorphicOrderAt_eq, hP₀]; simp
    refine ⟨?_, by simp [hp]⟩
    rw [hdiff z hz, hp, (hf z hz).meromorphicOrderAt_eq]
    cases he : analyticOrderAt f z with
    | top => simp
    | coe j =>
      rw [he] at hf₀
      have hle : n ≤ j := by exact_mod_cast hf₀
      exact WithTop.coe_le_coe.mpr (show (0 : ℤ) ≤ (j : ℤ) - (n : ℤ) by omega)
  have hF : AnalyticOnNhd ℂ F U := fun z hz ↦ (hnormal hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp (horders z hz).1
  refine ⟨F, hF, ?_, ?_⟩
  · intro z hz
    have hpn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hP z hz).meromorphicAt).mp (horders z hz).2
    have hev : (fun u ↦ P u * F u) =ᶠ[𝓝[≠] z] f := by
      filter_upwards [hm.toMeromorphicNFOn_eq_self_on_nhdsNE hz, hpn] with u hq hu
      change F u = f u / P u at hq
      rw [hq, mul_div_cancel₀ _ hu]
    have ht := (((hP z hz).continuousAt.mul (hF z hz).continuousAt).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {z}ᶜ))).congr' hev
    exact tendsto_nhds_unique ht ((hf z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  · intro z hz he
    obtain ⟨n, hPn, _⟩ := hord z hz
    apply (hnormal hz).meromorphicOrderAt_eq_zero_iff.mp
    rw [hdiff z hz, (hf z hz).meromorphicOrderAt_eq, (hP z hz).meromorphicOrderAt_eq, he, hPn]
    simp

/-- Removing all and exactly the zeros, counted with their finite analytic
orders, yields a holomorphic zero-free quotient, including at the removed roots. -/
private theorem exists_analytic_zero_free_quotient {U : Set ℂ} (g B : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g U) (hB : AnalyticOnNhd ℂ B U)
    (ho : ∀ z ∈ U, ∃ n : ℕ, analyticOrderAt g z = n ∧ analyticOrderAt B z = n) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q U ∧ (∀ z ∈ U, Q z ≠ 0) ∧
      ∀ z ∈ U, B z * Q z = g z := by
  obtain ⟨Q, hQ, hprod, hne⟩ := exists_analytic_quotient_of_order_le g B hg hB (fun z hz ↦ by
    obtain ⟨n, hgn, hBn⟩ := ho z hz
    exact ⟨n, hBn, hgn.ge⟩)
  refine ⟨Q, hQ, fun z hz ↦ ?_, hprod⟩
  obtain ⟨_, hgn, hBn⟩ := ho z hz
  exact hne z hz (hgn.trans hBn.symm)

private theorem bound_of_blaschke_mul {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ) * (1 - ‖a i‖))) (Q : ℂ → ℂ)
    (hQ : AnalyticOnNhd ℂ Q (ball 0 1)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖product a m z * Q z‖ ≤ M) :
    ∀ z ∈ ball (0 : ℂ) 1, ‖Q z‖ ≤ M := by
  intro z hz
  have hlim : Tendsto (fun S ↦ tail a m S z * Q z) atTop (𝓝 (Q z)) := by
    simpa using (tendsto_tail a m ha ha' hs (mem_ball_zero_iff.mp hz)).mul_const (Q z)
  apply le_of_tendsto' hlim.norm
  intro S
  let P := finiteProduct a m S
  let T := tail a m S
  obtain ⟨hP, hPb⟩ := finiteProduct_inner a m S ha ha'
  have hT : AnalyticOnNhd ℂ T (ball 0 1) := analyticOnNhd_tail a m S ha ha' hs
  apply disk_inner_multiplier_bound P (fun w ↦ T w * Q w) M hM hP hPb (hT.mul hQ) _ z hz
  intro w hw
  change ‖finiteProduct a m S w * (tail a m S w * Q w)‖ ≤ M
  rw [← mul_assoc, finiteProduct_mul_tail a m S ha ha' hs w hw]
  exact hb w hw

/-- A bounded analytic function on the unit disk factors as the full normalized
Blaschke product of its zeros with multiplicity times a bounded zero-free analytic
function. The analytic factor satisfies the same supremum bound as the original. -/
theorem exists_bounded_analytic_blaschke_quotient {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (hinj : Injective a) (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ) * (1 - ‖a i‖))) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g (ball 0 1)) (horder : ∀ i, analyticOrderAt g (a i) = m i)
    (hroots : ∀ z ∈ ball (0 : ℂ) 1, g z = 0 → ∃ i, a i = z)
    (M : ℝ) (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ M) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q (ball 0 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, Q z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, ‖Q z‖ ≤ M) ∧
      ∀ z ∈ ball (0 : ℂ) 1, product a m z * Q z = g z := by
  have hB : AnalyticOnNhd ℂ (product a m) (ball 0 1) := analyticOnNhd_product a m ha ha' hs
  have horders (z : ℂ) (hz : z ∈ ball 0 1) :
      ∃ n : ℕ, analyticOrderAt g z = n ∧ analyticOrderAt (product a m) z = n := by
    by_cases h : ∃ i, a i = z
    · obtain ⟨i, rfl⟩ := h
      exact ⟨m i, horder i, analyticOrderAt_product a m hinj ha ha' hs i⟩
    · have hg' : g z ≠ 0 := fun hh ↦ h (hroots z hz hh)
      have hB' := product_ne_zero a m ha ha' hs (mem_ball_zero_iff.mp hz)
        (fun i _ hi ↦ h ⟨i, hi.symm⟩)
      exact ⟨0, (hg z hz).analyticOrderAt_eq_zero.mpr hg', (hB z hz).analyticOrderAt_eq_zero.mpr hB'⟩
  obtain ⟨Q, hQ, hn, heq⟩ := exists_analytic_zero_free_quotient g (product a m) hg hB horders
  refine ⟨Q, hQ, hn, bound_of_blaschke_mul a m ha ha' hs Q hQ M ((norm_nonneg (g 0)).trans (hb _ (by simp))) ?_, heq⟩
  exact fun z hz ↦ (heq z hz) ▸ hb z hz

/-- The full normalized Blaschke product indexed by the actual zero set and
with the intrinsic analytic multiplicities of g. -/
def zeroProduct (g : ℂ → ℂ) : ℂ → ℂ :=
  product (fun i : {z : ℂ // z ∈ ball 0 1 ∧ g z = 0} ↦ i.val)
    (fun i ↦ analyticOrderNatAt g i.val)

/-- Canonical zero factorization from the bounded analytic function alone.
The full product uses the actual zero set and intrinsic orders; Jensen's formula
supplies the Blaschke condition automatically. -/
theorem exists_canonical_disk_factorization (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (ball 0 1))
    (h₀ : g 0 ≠ 0) (M : ℝ) (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ M) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q (ball 0 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, Q z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, ‖Q z‖ ≤ M) ∧
      ∀ z ∈ ball (0 : ℂ) 1, zeroProduct g z * Q z = g z := by
  let Z := {z : ℂ // z ∈ ball 0 1 ∧ g z = 0}
  let a (i : Z) : ℂ := i.val
  let m (i : Z) := analyticOrderNatAt g i.val
  have ha (i : Z) : a i ≠ 0 := by
    intro he
    have hzero : g (a i) = 0 := i.property.2
    exact h₀ (he ▸ hzero)
  have ha' (i : Z) : ‖a i‖ < 1 := mem_ball_zero_iff.mp i.property.1
  obtain ⟨horder, hs⟩ := disk_zero_orders_and_summability hg h₀ hb
  exact exists_bounded_analytic_blaschke_quotient a m Subtype.val_injective ha ha' hs g hg (fun i ↦ (horder i).2)
    (fun z hz hzero ↦ ⟨⟨z, hz, hzero⟩, rfl⟩) M hb

/-- Division by the finite Blaschke product of a prescribed set of roots of a
bounded analytic test preserves its bound. Only those finite vanishing jets are required. -/
theorem exists_bounded_finite_blaschke_quotient {ι : Type*} (a : ι → ℂ) (m : ι → ℕ) (S : Finset ι)
    (hinj : Injective a) (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (H : ℂ → ℂ) (hH : AnalyticOnNhd ℂ H (ball 0 1))
    (hv : ∀ i ∈ S, (m i : ℕ∞) ≤ analyticOrderAt H (a i))
    (M : ℝ) (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖H z‖ ≤ M) :
    ∃ N : ℂ → ℂ, AnalyticOnNhd ℂ N (ball 0 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, ‖N z‖ ≤ M) ∧
      ∀ z ∈ ball (0 : ℂ) 1, finiteProduct a m S z * N z = H z := by
  let P := finiteProduct a m S
  let a' (j : {i // i ∈ S}) := a j.val
  let m' (j : {i // i ∈ S}) := m j.val
  have hinj' : Injective a' := hinj.comp Subtype.val_injective
  have hsa : Summable (fun j ↦ (m' j : ℝ) * (1 - ‖a' j‖)) := (hasSum_fintype _).summable
  have he : product a' m' = P := product_subtype_mem a m S
  have hP : AnalyticOnNhd ℂ P (ball 0 1) := he ▸
    (analyticOnNhd_product a' m' (fun j ↦ ha _) (fun j ↦ ha' _) hsa : AnalyticOnNhd ℂ (product a' m') _)
  have horders (z : ℂ) (hz : z ∈ ball 0 1) : ∃ n : ℕ, analyticOrderAt P z = n ∧ ↑n ≤ analyticOrderAt H z := by
    by_cases h : ∃ j, a' j = z
    · obtain ⟨j, rfl⟩ := h
      refine ⟨m' j, ?_, hv _ j.property⟩
      rw [← he]
      exact analyticOrderAt_product a' m' hinj' (fun j ↦ ha _) (fun j ↦ ha' _) hsa j
    · refine ⟨0, (hP _ hz).analyticOrderAt_eq_zero.mpr ?_, by simp⟩
      rw [← he]
      exact product_ne_zero a' m' (fun j ↦ ha _) (fun j ↦ ha' _) hsa
        (mem_ball_zero_iff.mp hz) (fun j _ hj ↦ h ⟨j, hj.symm⟩)
  obtain ⟨N, hN, hprod, _⟩ := exists_analytic_quotient_of_order_le H P hH hP horders
  refine ⟨N, hN, ?_, hprod⟩
  obtain ⟨hPc, hPs⟩ := finiteProduct_inner a m S ha ha'
  exact disk_inner_multiplier_bound P N M ((norm_nonneg (H 0)).trans (hb 0 (by simp))) hPc hPs hN
    (fun z hz ↦ (hprod z hz) ▸ hb z hz)

/-- Given a finite set of tested zeros, the missing-zero tail times the test
is the original function times a bounded analytic numerator over a bounded
zero-free analytic denominator. The identity holds at the zeros as well. -/
theorem exists_tail_test_quotient {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (hinj : Injective a) (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ) * (1 - ‖a i‖))) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g (ball 0 1)) (horder : ∀ i, analyticOrderAt g (a i) = m i)
    (hroots : ∀ z ∈ ball (0 : ℂ) 1, g z = 0 → ∃ i, a i = z)
    (M : ℝ) (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ M) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q (ball 0 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, Q z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, ‖Q z‖ ≤ M) ∧
      ∀ (S : Finset ι) (H : ℂ → ℂ), AnalyticOnNhd ℂ H (ball 0 1) →
      (∀ i ∈ S, (m i : ℕ∞) ≤ analyticOrderAt H (a i)) →
      ∀ L : ℝ, (∀ z ∈ ball (0 : ℂ) 1, ‖H z‖ ≤ L) →
        ∃ N : ℂ → ℂ, AnalyticOnNhd ℂ N (ball 0 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, ‖N z‖ ≤ L) ∧
        ∀ z ∈ ball (0 : ℂ) 1, tail a m S z * H z = g z * (N z / Q z) := by
  obtain ⟨Q, hQ, hne, hbQ, hgQ⟩ := exists_bounded_analytic_blaschke_quotient a m hinj ha ha' hs g hg
    horder hroots M hb
  refine ⟨Q, hQ, hne, hbQ, ?_⟩
  intro S H hH hHv L hL
  obtain ⟨N, hN, hbN, heN⟩ := exists_bounded_finite_blaschke_quotient a m S hinj ha ha' H hH hHv L hL
  refine ⟨N, hN, hbN, ?_⟩
  intro z hz
  rw [← heN z hz, ← hgQ z hz, ← finiteProduct_mul_tail a m S ha ha' hs z hz]
  field_simp [hne z hz]

end RiemannMasullo.Blaschke
