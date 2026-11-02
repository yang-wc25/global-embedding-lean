import GlobalEmbedding.Paper.PhaseRegular
import GlobalEmbedding.Paper.IsometricMap
import GlobalEmbedding.Paper.Parallelizable
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.Maps.Basic

/-!
# The original closed parallelizable embedding target

Source: `literature/parallelizable-stable-plus-one/main.tex`, `thm:main`,
lines 110--120, and its concluding proof at lines 1094--1098.

The definition below imports only the source notions and Mathlib. It imports
no small-immersion, probes, repair or embedding-upgrade producer. Smooth
embedding is spelled out as smoothness, injective native differential and
an actual topological embedding. In particular, injectivity of the function
alone is not substituted for the embedding condition.

No nonemptiness, connectedness, orientability, chosen atlas, quantitative
phase margin, analytic provider or target conclusion is an input.
This is a statement definition, not a theorem that the statement holds.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Bundle Set Topology
open scoped ContDiff ENNReal

namespace GlobalEmbedding.Main
universe uM

/-- The full closed-source `thm:main`, with the same map supplying the exact
prescribed metric, phase regularity, immersion, embedding and image bound.
The ambient dimension is written literally as `n*(n+1)/2+1`. -/
def EndpointMainTarget : Prop :=
  ∀ {n : ℕ} {M : Type uM} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
    (_hn : 3 ≤ n)
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
      IsEmbedding F ∧ Set.range F ⊆ Metric.ball 0 r

end GlobalEmbedding.Main
