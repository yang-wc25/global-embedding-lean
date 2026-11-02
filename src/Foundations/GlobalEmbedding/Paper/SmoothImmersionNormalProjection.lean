import GlobalEmbedding.Paper.FixedChartSmoothNormalProjection

open Manifold Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- The actual normal projection field of a smooth immersion is smooth on its
original manifold, with its original finite-dimensional normed model.

Proof: in the fixed chart centered at x, the actual projection pullback is smooth
on an open target. Compose its smooth germ with the actual chart germ. On a source
neighborhood the chart inverse identity identifies this composite with the actual
normal projection. Smoothness is local, so the original field is smooth at every x.
Source: smooth actual normal bundle in `defn:phase`. -/
theorem smooth_immersion_normal_projection
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x)) :
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) ∞
      (fun x ↦ (normalSpace (I := I) f x).starProjection) := by
  intro x
  have hopen : IsOpen (extChartAt I x).target :=
    boundaryless_chart_target_open (I := I) (chartAt H x) (chart_mem_atlas H x)
  have hc := (fixed_chart_smooth_normal_projection f hf hinj x).contDiffAt
    (hopen.mem_nhds (mem_extChartAt_target x))
  have hcomp := hc.comp_contMDiffAt (contMDiffAt_extChartAt (I := I) (x := x))
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := I) x).mem_nhds
    (mem_extChartAt_source (I := I) x)]
    with y hy
  simp only [Function.comp_apply, (extChartAt I x).left_inv hy]

end GlobalEmbedding.Paper
