import GlobalEmbedding.Paper.GeneralMaximalChartRangeNeighborhood
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, true normal second forms. -/

open Filter Manifold Set
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- A maximal-atlas transition takes the actual chart differential of a tangent vector
back to the centered model tangent vector.
Proof: the centered extended chart equals the transition after the selected extended
chart near x. Differentiate this local identity and use the centered-chart identity
for the manifold differential. Source: `defn:phase`, both arguments in the chart formula. -/
theorem general_chart_transition_tangent_transport
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [BoundarylessManifold I M] (x : M) (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I 2 M) (hx : x ∈ e.source)
    (v : TangentSpace I x) :
    fderiv ℝ ((extChartAt I x) ∘ (e.extend I).symm) (e.extend I x)
      (tangentSpaceCastModel 𝓘(ℝ, E) (e.extend I x)
        (mfderiv I 𝓘(ℝ, E) (e.extend I) x v)) = tangentSpaceCastModel I x v := by
  have hr := general_maximal_chart_range_mem_nhds (I := I) e he x hx
  have ht0 := I.contDiffWithinAt_extendCoordChange' he
    (IsManifold.chart_mem_maximalAtlas (I := I) (n := 2) x) hx (mem_chart_source H x)
  have ht : DifferentiableAt ℝ ((extChartAt I x) ∘ (e.extend I).symm) (e.extend I x) :=
    (ht0.contDiffAt hr).differentiableAt (by norm_num)
  have he1 : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) he
  have hE : MDifferentiableAt I 𝓘(ℝ, E) (e.extend I) x :=
    (e.contMDiffAt_extend he1 hx).mdifferentiableAt (by norm_num)
  have heq : (extChartAt I x) =ᶠ[𝓝 x]
      ((extChartAt I x) ∘ (e.extend I).symm) ∘ (e.extend I) := by
    filter_upwards [e.extend_source_mem_nhds (I := I) hx] with p hp
    change extChartAt I x p = extChartAt I x ((e.extend I).symm (e.extend I p))
    rw [(e.extend I).left_inv hp]
  have hd := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, E))
  rw [mfderiv_extChartAt_self, mfderiv_comp x ht.mdifferentiableAt hE,
    mfderiv_eq_fderiv] at hd
  have hv := congrArg (fun L : TangentSpace I x →L[ℝ] E ↦ L v) hd
  exact hv.symm

end GlobalEmbedding.Paper
