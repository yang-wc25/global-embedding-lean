import GlobalEmbedding.Paper.InducedMetric
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# An internal auxiliary norm on the reference tangent fibers

The native reference factory uses a `RiemannianBundle` only to put a norm
on each tangent fiber.  That class does not require continuity with respect
to the base point.  The existing tangent-model identification therefore
supplies it directly.  No auxiliary metric or norm is requested from the
original probe entrance, and no smooth-bundle assertion is made here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Manifold Bundle Bornology
open scoped ContDiff Topology RealInnerProductSpace

namespace GlobalEmbedding.Continuation.UpgradeContinuation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "IM" => 𝓘(ℝ,D)

/-- The model inner product on each native tangent fiber.  This is an
auxiliary fiber norm, with no additional manifold hypothesis. -/
@[instance_reducible] def referenceRiemannianBundle : RiemannianBundle (TangentSpace IM : M → Type _) :=
  ⟨{
    inner := fun _ => (innerSL ℝ (E := D) : D →L[ℝ] D →L[ℝ] ℝ)
    symm := by
      intro x v w
      change inner ℝ (show D from v) (show D from w) = inner ℝ (show D from w) (show D from v)
      exact real_inner_comm _ _
    pos := by
      intro x v hv
      change 0 < inner ℝ (show D from v) (show D from v)
      exact real_inner_self_pos.2 hv
    continuousAt := by
      intro x
      change ContinuousAt (fun v : D => inner ℝ v v) 0
      exact (continuous_id.inner continuous_id).continuousAt
    isVonNBounded := by
      intro x
      change IsVonNBounded ℝ {v : D | inner ℝ v v < 1}
      have hball : Metric.ball (0 : D) 1 = {v : D | inner ℝ v v < 1} := by
        ext v
        simp only [Metric.mem_ball, dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := ℝ),
          RCLike.re_to_real, Set.mem_ofPred_eq]
        conv_lhs => rw [show (1 : ℝ) = √1 by simp]
        rw [Real.sqrt_lt_sqrt_iff]
        exact real_inner_self_nonneg
      rw [← hball]
      exact NormedSpace.isVonNBounded_ball ℝ D 1 }⟩

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.referenceRiemannianBundle
