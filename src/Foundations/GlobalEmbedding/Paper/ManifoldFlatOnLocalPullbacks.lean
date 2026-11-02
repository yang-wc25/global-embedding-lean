import GlobalEmbedding.Paper.ManifoldFlatOn
import GlobalEmbedding.Paper.GeneralMaximalChartRangeNeighborhood

open Manifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- Actual vanishing jets after every smooth local parameterization imply the
source flatness predicate. This criterion consumes local flat cutoff proofs.

Proof: each actual maximal inverse chart is a smooth local parameterization:
boundarylessness makes its model inverse smooth at the chart point. Compose
with the actual smooth chart inverse and use its inverse law. Source:
`prop:matrix`, flatness of the curvature cutoff on its zero set. -/
theorem manifold_flat_on_of_local_pullbacks
    {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : M → F) (Z : Set M) (hf : ContMDiff I 𝓘(ℝ, F) ∞ f)
    (hflat : ∀ (g : E → M) (p : E), ContMDiffAt 𝓘(ℝ, E) I ∞ g p → g p ∈ Z →
      ∀ k : ℕ, iteratedFDeriv ℝ k (f ∘ g) p = 0) :
    ManifoldFlatOn (I := I) f Z := by
  refine ⟨hf, ?_⟩
  intro x hx e he hex k
  have he2 : e ∈ IsManifold.maximalAtlas I 2 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have hr := general_maximal_chart_range_mem_nhds e he2 x hex
  have hI : ContMDiffAt 𝓘(ℝ, E) I ∞ I.symm (e.extend I x) :=
    I.contMDiffOn_symm.contMDiffAt hr
  have hmem : I.symm (e.extend I x) ∈ e.target := by
    simpa only [OpenPartialHomeomorph.extend_coe, Function.comp_apply, I.left_inv] using e.map_source hex
  have hE := contMDiffAt_symm_of_mem_maximalAtlas he hmem
  have hg : ContMDiffAt 𝓘(ℝ, E) I ∞ (e.extend I).symm (e.extend I x) :=
    hE.comp (e.extend I x) hI
  apply hflat (e.extend I).symm (e.extend I x) hg
  simpa only [(e.extend I).left_inv (by simpa only [OpenPartialHomeomorph.extend_source] using hex)] using hx

end GlobalEmbedding.Paper
