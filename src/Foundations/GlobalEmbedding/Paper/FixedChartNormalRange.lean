import GlobalEmbedding.Paper.NormalSpace
import GlobalEmbedding.Paper.GeneralChartPushforward

open Manifold Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- The actual normal space at every point in a fixed chart is exactly the
orthogonal complement of the actual full fixed-coordinate derivative range.

Proof: the proved general-I pushforward identity expresses the actual manifold
differential as the fixed-coordinate derivative composed with the actual chart
differential and model cast. The latter are surjective because a chart differential
is invertible and the model cast is an equivalence. Thus the two ranges coincide;
take their actual orthogonal complements.
Source: fixed-chart smooth normal-projection formula expanding `defn:phase`. -/
theorem normalSpace_eq_fixed_chart_range_orthogonal
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N)) (y : M) (z : E)
    (hz : z ∈ (extChartAt I y).target)
    (hf : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f
      ((extChartAt I y).symm z)) :
    normalSpace (I := I) f ((extChartAt I y).symm z) =
      (LinearMap.range (fderiv ℝ (f ∘ (extChartAt I y).symm) z).toLinearMap)ᗮ := by
  let x := (extChartAt I y).symm z
  let castF := tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f x)
  let D := castF.toContinuousLinearMap.comp
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x)
  let C := fderiv ℝ (f ∘ (extChartAt I y).symm) z
  let T := (tangentSpaceCastModel 𝓘(ℝ, E) z).toContinuousLinearMap.comp
    (mfderiv I 𝓘(ℝ, E) (extChartAt I y) x)
  have hDC (v : TangentSpace I x) : D v = C (T v) :=
    general_chart_pushforward_pointwise f y z hz hf v
  have hsurj : Function.Surjective T :=
    (tangentSpaceCastModel 𝓘(ℝ, E) z).surjective.comp
      (isInvertible_mfderiv_extChartAt ((extChartAt I y).map_target hz)).surjective
  have hrange : LinearMap.range D.toLinearMap = LinearMap.range C.toLinearMap := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨T v, (hDC v).symm⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨u, hu⟩ := hsurj v
      exact ⟨u, (hDC u).trans (congrArg C hu)⟩
  change (LinearMap.range D.toLinearMap)ᗮ = (LinearMap.range C.toLinearMap)ᗮ
  rw [hrange]

end GlobalEmbedding.Paper
