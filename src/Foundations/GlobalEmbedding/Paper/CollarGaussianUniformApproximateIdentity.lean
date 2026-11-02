import GlobalEmbedding.Paper.CollarGaussianNormalizedTail
import Mathlib.Analysis.Convolution

/-!
# Global uniform Gaussian approximation of bounded uniformly continuous functions

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof line 520. The global uniform estimate is stronger than pointwise approximate-identity
convergence and is needed for each derivative in the global Ck approximation.
-/

open MeasureTheory Filter Metric Set
open scoped Topology

namespace GlobalEmbedding.Paper

/-- The source normalized Gaussian convolutions of a bounded uniformly continuous function
converge uniformly on the whole Euclidean domain to that actual function.

Source: Proposition `prop:collar`, proof line 520; global uniform approximation detail.
The actual Gaussian normalization and tails are supplied by the proved normalization theorem.
Uniform continuity gives one δ controlling h(x-y)-h(x) for every x when norm(y)<δ. A global
bound C controls this difference by 2C elsewhere. Rewrite the convolution error using actual
unit mass and translation-invariant integration. Its norm is bounded uniformly in x by η/2
plus 2C times the actual Gaussian mass on norm(y)≥δ. That tail tends to zero, giving the
global uniform limit. Integrability follows from the actual integrable kernel and bounded
continuous shifted values, so no compact-support or integrability hypothesis on h is added.
The target is any real Banach space, and domain dimension zero is included. -/
theorem collar_gaussian_uniform_approximate_identity
    {d : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (h : EuclideanSpace ℝ (Fin d) → W) (huc : UniformContinuous h)
    (C : ℝ) (hC : ∀ x, ‖h x‖ ≤ C) :
    TendstoUniformly
      (fun (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) ↦
        ∫ y : EuclideanSpace ℝ (Fin d),
          ((Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / ε)) • h y)
      h (𝓝[>] 0) := by
  let V := EuclideanSpace ℝ (Fin d)
  let K : ℝ → V → ℝ := fun ε x ↦
    (Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / ε)
  obtain ⟨hk, htail⟩ := collar_gaussian_normalized_tail d
  change (∀ ε : ℝ, 0 < ε → (∀ x, 0 ≤ K ε x) ∧ Integrable (K ε) ∧ ∫ x, K ε x = 1) at hk
  change ∀ δ : ℝ, 0 < δ →
    Tendsto (fun ε : ℝ ↦ ∫ x in {x | δ ≤ ‖x‖}, K ε x) (𝓝[>] 0) (𝓝 0) at htail
  have hC0 : 0 ≤ C := (norm_nonneg (h 0)).trans (hC 0)
  apply Metric.tendstoUniformly_iff.mpr
  intro η hη
  obtain ⟨δ, hδ, hδh⟩ := Metric.uniformContinuous_iff.mp huc (η / 2) (by positivity)
  have ht : Tendsto (fun ε : ℝ ↦
      (2 * C) * (∫ y in {y : V | δ ≤ ‖y‖}, K ε y)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (htail δ hδ).const_mul (2 * C)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (2 * C) * (∫ y in {y : V | δ ≤ ‖y‖}, K ε y) < η / 2 :=
    ht.eventually (gt_mem_nhds (by positivity))
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε (hε : 0 < ε) hεsmall
  intro x
  obtain ⟨hkn, hki, hmass⟩ := hk ε hε
  have hswap : (∫ y, K ε (x - y) • h y) = ∫ y, K ε y • h (x - y) := by
    simpa only [sub_sub_cancel] using
      integral_sub_left_eq_self (fun y : V ↦ K ε y • h (x - y)) volume x
  have hshift : Continuous (fun y : V ↦ h (x - y)) :=
    huc.continuous.comp (continuous_const.sub continuous_id)
  have hi : Integrable (fun y : V ↦ K ε y • h (x - y)) :=
    hki.smul_bdd C hshift.aestronglyMeasurable (ae_of_all _ (fun y ↦ hC (x - y)))
  have herr : (∫ y, K ε y • h (x - y)) - h x =
      ∫ y, K ε y • (h (x - y) - h x) := by
    rw [show (fun y : V ↦ K ε y • (h (x - y) - h x)) =
        (fun y ↦ K ε y • h (x - y) - K ε y • h x) by
      ext y
      exact smul_sub _ _ _]
    rw [integral_sub hi (hki.smul_const (h x)), integral_smul_const, hmass, one_smul]
  let S : Set V := {y | δ ≤ ‖y‖}
  have hS : MeasurableSet S := measurableSet_le measurable_const measurable_norm
  let b : V → ℝ := fun y ↦ (η / 2) * K ε y + (2 * C) * S.indicator (K ε) y
  have hbi : Integrable b :=
    (hki.const_mul (η / 2)).add ((hki.indicator hS).const_mul (2 * C))
  have hb (y : V) : ‖K ε y • (h (x - y) - h x)‖ ≤ b y := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hkn y)]
    by_cases hy : y ∈ S
    · have hd : ‖h (x - y) - h x‖ ≤ 2 * C :=
        (norm_sub_le _ _).trans (by linarith [hC (x - y), hC x])
      have hη0 : 0 ≤ (η / 2) * K ε y := mul_nonneg (by positivity) (hkn y)
      dsimp only [b]
      rw [indicator_of_mem hy]
      nlinarith only [mul_le_mul_of_nonneg_left hd (hkn y), hη0]
    · have hnorm : ‖y‖ < δ := lt_of_not_ge hy
      have hdist : dist (x - y) x < δ := by simpa [dist_eq_norm] using hnorm
      have hval : ‖h (x - y) - h x‖ < η / 2 := by
        simpa only [dist_eq_norm] using hδh hdist
      dsimp only [b]
      rw [indicator_of_notMem hy, mul_zero, add_zero]
      nlinarith only [mul_le_mul_of_nonneg_left hval.le (hkn y)]
  have hbound : ‖∫ y, K ε y • (h (x - y) - h x)‖ ≤
      η / 2 + (2 * C) * (∫ y in S, K ε y) := by
    calc
      _ ≤ ∫ y, b y := norm_integral_le_of_norm_le hbi (ae_of_all _ hb)
      _ = _ := by
        dsimp only [b]
        rw [integral_add (hki.const_mul (η / 2)) ((hki.indicator hS).const_mul (2 * C))]
        rw [integral_const_mul (η / 2) (K ε),
          integral_const_mul (2 * C) (S.indicator (K ε)), hmass, mul_one,
          integral_indicator hS]
  change dist (h x) (∫ y, K ε (x - y) • h y) < η
  rw [dist_eq_norm, norm_sub_rev, hswap, herr]
  exact hbound.trans_lt (by linarith only [hεsmall])

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_gaussian_uniform_approximate_identity
