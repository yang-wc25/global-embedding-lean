import GlobalEmbedding.Paper.GeneralChartPushforward

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Actual immersion differential injectivity implies injectivity of the full
derivative in any fixed actual chart on a boundaryless manifold.

Proof: the general-I pushforward identity writes the actual differential as the
coordinate derivative composed with the chart differential and model cast. That
chart composite is surjective. Lift two coordinate vectors to tangent vectors;
equality of coordinate derivative values implies equality under the actual
differential, hence equality of lifts by immersion injectivity. Their chart images
are the original coordinate vectors.
Source: fixed-coordinate immersion frames expanding `defn:phase`. -/
theorem fixed_chart_derivative_injective
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N)) (y : M) (z : E)
    (hz : z ∈ (extChartAt I y).target)
    (hf : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f
      ((extChartAt I y).symm z))
    (hinj : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f
      ((extChartAt I y).symm z))) :
    Function.Injective (fderiv ℝ (f ∘ (extChartAt I y).symm) z) := by
  let x := (extChartAt I y).symm z
  let T := (tangentSpaceCastModel 𝓘(ℝ, E) z).toContinuousLinearMap.comp
    (mfderiv I 𝓘(ℝ, E) (extChartAt I y) x)
  have hsurj : Function.Surjective T :=
    (tangentSpaceCastModel 𝓘(ℝ, E) z).surjective.comp
      (isInvertible_mfderiv_extChartAt ((extChartAt I y).map_target hz)).surjective
  intro u v huv
  obtain ⟨a, ha⟩ := hsurj u
  obtain ⟨b, hb⟩ := hsurj v
  have hab : a = b := by
    apply hinj
    apply (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f x)).injective
    rw [general_chart_pushforward_pointwise f y z hz hf a,
      general_chart_pushforward_pointwise f y z hz hf b]
    change fderiv ℝ (f ∘ (extChartAt I y).symm) z (T a) =
      fderiv ℝ (f ∘ (extChartAt I y).symm) z (T b)
    rw [ha, hb]
    exact huv
  exact ha.symm.trans ((congrArg T hab).trans hb)

end GlobalEmbedding.Paper
