import Upgrade.CompactScaleSelection
import Upgrade.ProbeInterface
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Actual original-C² and finite response scales

The parameter ball is fixed first. All finite response budgets are then valid
at that radius itself, so they can be passed to the prepared-region null-set
consumers. Original C² closeness is uniform on the full admitted probe ball.
-/

noncomputable section
open Set Filter Bundle Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade

theorem finite_probe_error_radius_then_scale
    {ι : Type*} [Fintype ι]
    (eta : ι → ℝ → ℝ) (C margin : ι → ℝ)
    (heta : ∀ i, Tendsto (eta i) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hmargin : ∀ i, 0 < margin i) :
    ∃ rho > 0, ∃ t0 > 0, ∀ t, 0 < t → t < t0 →
      ∀ i, eta i t + C i * rho < margin i := by
  obtain ⟨r, hr, t0, ht0, hbound⟩ :=
    finite_probe_parameter_ball_then_scale (U := ℝ) eta C margin heta hmargin
  refine ⟨r / 2, half_pos hr, t0, ht0, ?_⟩
  intro t ht htt i
  have hu : ‖r / 2‖ < r := by
    rw [Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  have h := hbound t ht htt (r / 2) hu i
  rw [Real.norm_eq_abs, abs_of_pos (half_pos hr)] at h
  exact (add_le_add (le_abs_self _) (mul_le_mul_of_nonneg_right (le_abs_self _) (half_pos hr).le)).trans_lt h

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem ExactProbeFamily.eventually_originalC2_small
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F hF}
    (probe : ExactProbeFamily F hF A waves) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ t0 > 0, t0 ≤ probe.threshold ∧ ∀ t, 0 < t → t < t0 →
      ∀ u, ‖u‖ < probe.radius → probeAtlasCj A 2 (probe.map t u - F) ≤ ENNReal.ofReal epsilon := by
  have hsigma : Tendsto (fun t : ℝ ↦ t ^ ((44 : ℝ) / 5)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuous_rpow_const (q := (44 : ℝ) / 5) (by positivity)).tendsto (0 : ℝ)
    simpa only [Real.zero_rpow (by norm_num : (44 : ℝ) / 5 ≠ 0)] using
      h.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), probe.constant * t ^ ((44 : ℝ) / 5) < epsilon :=
    (tendsto_order.mp (by simpa only [mul_zero] using hsigma.const_mul probe.constant)).2 epsilon hepsilon
  obtain ⟨s, hs, hbound⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hsmall
  refine ⟨min s probe.threshold, lt_min hs probe.threshold_pos, min_le_right _ _, ?_⟩
  intro t ht htt u hu
  exact (probe.closeness t ht (htt.trans_le (min_le_right _ _)) u hu).trans
    (ENNReal.ofReal_le_ofReal (hbound ⟨ht, htt.trans_le (min_le_left _ _)⟩).le)

end GlobalEmbedding.Upgrade
