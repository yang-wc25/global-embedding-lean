import GlobalEmbedding.Paper.BoundarylessChartTargetOpen
import GlobalEmbedding.Paper.FixedChartNormalRange
import GlobalEmbedding.Paper.FixedChartDerivativeInjective
import GlobalEmbedding.Paper.SmoothNormedFrameNormalProjection
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual normal-space projection of a smooth immersion varies smoothly in
each fixed actual chart, for arbitrary finite-dimensional normed manifold models.

Proof: the fixed-coordinate representative of f is smooth on the actual extended
chart target, which is open by actual manifold boundarylessness. Its derivative
field is smooth and injective by the actual immersion-to-coordinate bridge. Smooth
finite-normed-frame projection therefore applies. The fixed-chart normal-space
range identity identifies these actual projections with the actual normalSpace
projections. No global boundarylessness of I or inner product on the model E is used.
Source: smooth actual normal field in `defn:phase`. -/
theorem fixed_chart_smooth_normal_projection
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x))
    (y : M) :
    ContDiffOn ℝ ∞
      (fun z ↦ (normalSpace (I := I) f ((extChartAt I y).symm z)).starProjection)
      (extChartAt I y).target := by
  have hF : ContDiffOn ℝ ∞ (f ∘ (extChartAt I y).symm) (extChartAt I y).target :=
    (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm y)).contDiffOn
  have hopen : IsOpen (extChartAt I y).target :=
    boundaryless_chart_target_open (I := I) (chartAt H y) (chart_mem_atlas H y)
  have hD := hF.fderiv_of_isOpen hopen (m := ∞) (by simp)
  have hcoord : ∀ z ∈ (extChartAt I y).target,
      Function.Injective (fderiv ℝ (f ∘ (extChartAt I y).symm) z) := by
    intro z hz
    exact fixed_chart_derivative_injective f y z hz
      (hf.mdifferentiable (by simp) _) (hinj _)
  have h := smooth_normed_frame_normal_projection _ hD hcoord
  apply h.congr
  intro z hz
  rw [normalSpace_eq_fixed_chart_range_orthogonal f y z hz
    (hf.mdifferentiable (by simp) _)]

end GlobalEmbedding.Paper
