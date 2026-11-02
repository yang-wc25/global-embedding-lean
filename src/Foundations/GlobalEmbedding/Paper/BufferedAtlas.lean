import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Finite buffered atlases

Source: `literature/parallelizable-stable-plus-one/main.tex`, notation on finite buffered atlases
and Setup `setup:uniform`, lines 234 and 591; DAG node `initialization-buffered-atlas`.
-/

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Raw finite topological chart data with open inner domains covering `M` and one positive coordinate
buffer. This alone does not assert smooth compatibility or support containment; the paper
notion additionally requires `IsSmoothBufferedAtlas`. The balls in the buffer condition are contained in the corresponding chart targets.
The `support` sets are specified independently: they are not assumed to be chart domains, closed,
or contained in any other set. The atlas may be empty, in which case the cover requires `M` to be
empty. Source: notation on finite buffered atlases and Setup `setup:uniform`, lines 234 and 591. -/
structure BufferedAtlas (M E : Type*) [TopologicalSpace M] [PseudoMetricSpace E] where
  /-- Number of charts. -/
  count : ℕ
  /-- Coordinate maps, with their open source and target. -/
  chart : Fin count → OpenPartialHomeomorph M E
  /-- Inner chart domains. -/
  inner : Fin count → Set M
  /-- The inner domains are open. -/
  inner_open : ∀ i, IsOpen (inner i)
  /-- Each inner domain lies in its coordinate domain. -/
  inner_subset : ∀ i, inner i ⊆ (chart i).source
  /-- The inner domains cover the source. -/
  cover : ∀ x, ∃ i, x ∈ inner i
  /-- One common positive coordinate buffer. -/
  buffer : ℝ
  /-- The buffer is positive, including for an empty atlas. -/
  buffer_pos : 0 < buffer
  /-- Every inner coordinate image has the prescribed buffer in the chart target. -/
  buffered : ∀ i x, x ∈ inner i → Metric.ball (chart i x) buffer ⊆ (chart i).target
  /-- The separately specified enlarged chart supports. -/
  support : Fin count → Set M

/-- The paper's smooth buffered atlas condition: every chart belongs to the maximal smooth
atlas of the given manifold structure, and each enlarged support lies in its chart source.
Maximal-atlas membership guarantees smoothness of each chart and its inverse on their domains.
No closedness or equality between support and source is imposed. Source: notation on finite
buffered atlases and Setup `setup:uniform`, lines 234 and 591. -/
structure IsSmoothBufferedAtlas {M E : Type*} [TopologicalSpace M] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (A : BufferedAtlas M E) : Prop where
  /-- Each chart is compatible with the specified smooth structure. -/
  chart_mem : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M
  /-- Enlarged supports are subordinate to their coordinate sources. -/
  support_subset : ∀ i, A.support i ⊆ (A.chart i).source

/-- The simple intersection graph of the specified enlarged supports: distinct indices are
adjacent precisely when their supports meet. Source: Setup `setup:uniform`, line 591. -/
def BufferedAtlas.supportGraph {M E : Type*} [TopologicalSpace M] [PseudoMetricSpace E]
    (A : BufferedAtlas M E) : SimpleGraph (Fin A.count) where
  Adj i j := i ≠ j ∧ (A.support i ∩ A.support j).Nonempty
  symm := ⟨fun _ _ h ↦ ⟨Ne.symm h.1, by simpa [Set.inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Maximum degree of the support intersection graph, counting other indices only. It is zero
for an empty atlas and for a one-chart atlas. Source: Setup `setup:uniform`, line 591. -/
noncomputable def BufferedAtlas.supportDegree {M E : Type*} [TopologicalSpace M]
    [PseudoMetricSpace E] (A : BufferedAtlas M E) : ℕ := by
  classical
  exact Finset.univ.sup (fun i ↦ A.supportGraph.degree i)



end GlobalEmbedding.Paper
