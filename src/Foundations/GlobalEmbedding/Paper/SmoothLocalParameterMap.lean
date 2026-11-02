import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A global smooth parameter map into an open set, locally equal to identity

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-local-parameter-map`.
-/

open Set Metric
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- Near each point of a Euclidean open parameter set there is a global genuine C∞ map into
that set which agrees with the identity near the point.

Choose a ball inside the open set and a genuine smooth bump χ with values in [0,1], equal to
one on a smaller ball and supported in the original ball. The map R(p)=p₀+χ(p)(p−p₀) is smooth,
has range in that convex ball or at p₀, and is identity near p₀.
Source: localization of smooth parameter families in the proof of `lem:balanced`. -/
theorem smooth_local_parameter_map {q : ℕ} (U : Set (EuclideanSpace ℝ (Fin q)))
    (hU : IsOpen U) (p₀ : EuclideanSpace ℝ (Fin q)) (hp₀ : p₀ ∈ U) :
    ∃ R : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin q),
      ContDiff ℝ ∞ R ∧ (∀ p, R p ∈ U) ∧ R =ᶠ[𝓝 p₀] id := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU p₀ hp₀
  let χ : ContDiffBump p₀ :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  let R (p : EuclideanSpace ℝ (Fin q)) := p₀ + χ p • (p - p₀)
  refine ⟨R, contDiff_const.add (χ.contDiff.smul (contDiff_id.sub contDiff_const)), ?_, ?_⟩
  · intro p
    by_cases hχ : χ p = 0
    · simpa only [R, hχ, zero_smul, add_zero] using hp₀
    · have hpball : p ∈ ball p₀ r := by
        change p ∈ ball p₀ χ.rOut
        rw [← χ.support_eq]
        exact hχ
      apply hball
      rw [mem_ball, dist_eq_norm]
      change ‖p₀ + χ p • (p - p₀) - p₀‖ < r
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg χ.nonneg]
      exact ((mul_le_mul_of_nonneg_right χ.le_one (norm_nonneg _)).trans_eq
        (one_mul _)).trans_lt (by simpa only [mem_ball, dist_eq_norm] using hpball)
  · filter_upwards [Metric.closedBall_mem_nhds p₀ (half_pos hr)] with p hp
    change p₀ + χ p • (p - p₀) = p
    rw [χ.one_of_mem_closedBall hp, one_smul]
    abel

#print axioms smooth_local_parameter_map

end GlobalEmbedding.Paper
