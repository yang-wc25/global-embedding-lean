import GlobalEmbedding.Paper.GeneralMaximalChartRangeNeighborhood
import GlobalEmbedding.Paper.GeneralChartContDiff
import GlobalEmbedding.Paper.NormalProjectionGeneralChartDerivative
import GlobalEmbedding.Paper.ProjectedHessianChain

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, chart-independence of the normal second form. -/

open Filter Manifold Set
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- General-I atlas transitions preserve the normal-projected Hessian.
Proof: the coordinate representatives agree locally after transition. C² of the
transition holds within range I, which is a neighborhood by the preceding lemma.
The second-order chain rule adds a first-derivative-image term, killed by the proved
general-I normal projection formula.
Source: `defn:phase`, chart-independence of the normal second form. -/
theorem normal_projected_hessian_general_maximal_chart
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N)) (x : M)
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I 2 M) (hx : x ∈ e.source)
    (hf : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 2 f x) (v w : E) :
    (normalSpace (I := I) f x).starProjection
      (fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm)) (e.extend I x) v w) =
    (normalSpace (I := I) f x).starProjection
      (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x)
        (fderiv ℝ ((extChartAt I x) ∘ (e.extend I).symm) (e.extend I x) v)
        (fderiv ℝ ((extChartAt I x) ∘ (e.extend I).symm) (e.extend I x) w)) := by
  have hr := general_maximal_chart_range_mem_nhds (I := I) e he x hx
  have hfc := contDiffAt_general_chart_representative hf
  have ht0 := I.contDiffWithinAt_extendCoordChange'
    he
    (IsManifold.chart_mem_maximalAtlas (I := I) (n := 2) x)
    hx (mem_chart_source H x)
  have ht : ContDiffAt ℝ 2 ((extChartAt I x) ∘ (e.extend I).symm) (e.extend I x) := by
    exact ht0.contDiffAt hr
  have heq : (f ∘ (e.extend I).symm) =ᶠ[𝓝 (e.extend I x)]
      (f ∘ (extChartAt I x).symm) ∘ ((extChartAt I x) ∘ (e.extend I).symm) := by
    filter_upwards [e.extend_preimage_mem_nhds hx (extChartAt_source_mem_nhds (I := I) x)] with z hz
    change f ((e.extend I).symm z) =
      f ((extChartAt I x).symm (extChartAt I x ((e.extend I).symm z)))
    rw [(extChartAt I x).left_inv hz]
  have hb : (extChartAt I x) ((e.extend I).symm (e.extend I x)) = extChartAt I x x := by
    rw [e.extend_left_inv hx]
  have hp : ∀ z : E, (normalSpace (I := I) f x).starProjection
      (fderiv ℝ (f ∘ (extChartAt I x).symm)
        ((extChartAt I x) ((e.extend I).symm (e.extend I x))) z) = 0 := by
    intro z
    rw [hb, Submodule.starProjection_apply,
      normal_projection_general_chart_derivative f x (hf.mdifferentiableAt (by norm_num)) z]
    rfl
  rw [heq.fderiv.fderiv_eq]
  have hfc' : ContDiffAt ℝ 2 (f ∘ (extChartAt I x).symm)
      ((extChartAt I x) ((e.extend I).symm (e.extend I x))) := by
    simpa only [hb] using hfc
  simpa only [Function.comp_apply, hb] using
    projected_hessian_chain (f ∘ (extChartAt I x).symm)
      ((extChartAt I x) ∘ (e.extend I).symm)
      (normalSpace (I := I) f x).starProjection (e.extend I x) hfc' ht hp v w

end GlobalEmbedding.Paper
