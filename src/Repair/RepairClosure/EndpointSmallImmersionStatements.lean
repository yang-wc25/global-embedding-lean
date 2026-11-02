import GlobalEmbedding.Paper.PhaseRegular
import GlobalEmbedding.Paper.IsometricMap
import GlobalEmbedding.Paper.Parallelizable
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Independent complete source target for small exact immersions

Source: main.tex, prop:initialization and cor:small-immersion, 787--835.
This file imports only original geometric definitions and the standard
smooth Riemannian metric type. It imports no initialization, repair,
rescaling or small-immersion producer, including the empty-source producer.

The target is handwritten as one complete forall expression. Its same F
has all five original properties. The ambient dimension and strict uniform
image bound are spelled out, and there is no connectedness, nonemptiness,
chosen atlas, quantitative reserve or repair-supplier premise.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Bundle
open scoped ContDiff ENNReal

namespace GlobalEmbedding.Continuation.RepairClosure
universe uM

/-- The literal original corollary, including arbitrary radius, disconnected
closed parallelizable sources, the given metric and a single smooth map. -/
def EndpointSmallExactImmersionTarget : Prop :=
  ∀ {n : ℕ} {M : Type uM} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
    (_hn : 2 ≤ n)
    (_hpar : IsParallelizable (M := M) 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) n)
    (metric0 : ContMDiffRiemannianMetric 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) : M → Type _))
    (r : ℝ) (_hr : 0 < r),
    ∃ F : M → EuclideanSpace ℝ (Fin (n*(n+1)/2+1)),
    ∃ hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
      𝓘(ℝ,EuclideanSpace ℝ (Fin (n*(n+1)/2+1))) ∞ F,
      inducedMetric (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin n))) F =
        (fun x => (metric0.inner x).toLinearMap₁₂) ∧
      (∀ x, Function.Injective
        (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
          𝓘(ℝ,EuclideanSpace ℝ (Fin (n*(n+1)/2+1))) F x)) ∧
      PhaseRegular (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin n))) F hF ∧
      (⨆ x : M, ENNReal.ofReal ‖F x‖) < ENNReal.ofReal r

end GlobalEmbedding.Continuation.RepairClosure
