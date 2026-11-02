import GlobalEmbedding.Paper.NormalSpace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open Manifold

namespace GlobalEmbedding.Paper

/-- The actual normal space of an injective immersion differential has rank
ambient dimension minus the original model dimension.

Proof: compose the actual differential with the ambient tangent model cast. It
remains injective, hence its actual range has the tangent-space dimension, which
equals the model dimension via the tangent model equivalence. The actual normal
space is its orthogonal complement. Add complementary dimensions in the actual
Euclidean ambient space and subtract in the natural numbers.
Source: constant actual normal rank in `defn:phase`. -/
theorem immersion_normal_rank
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N)) (x : M)
    (hinj : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x)) :
    Module.finrank ℝ (normalSpace (I := I) f x) = N - Module.finrank ℝ E := by
  let castF := tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f x)
  let D := castF.toContinuousLinearMap.comp
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x)
  have hD : Function.Injective D := castF.injective.comp hinj
  have hrange : Module.finrank ℝ (LinearMap.range D.toLinearMap) =
      Module.finrank ℝ E :=
    (LinearMap.finrank_range_of_inj hD).trans
      (tangentSpaceCastModel I x).toLinearEquiv.finrank_eq
  have hsum := (LinearMap.range D.toLinearMap).finrank_add_finrank_orthogonal
  change Module.finrank ℝ (LinearMap.range D.toLinearMap) +
    Module.finrank ℝ (normalSpace (I := I) f x) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) at hsum
  rw [hrange, finrank_euclideanSpace_fin] at hsum
  omega

end GlobalEmbedding.Paper
