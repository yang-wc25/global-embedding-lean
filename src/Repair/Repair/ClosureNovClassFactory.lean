import Repair.ClosureNovFixedClass
import Repair.ClosureNovWeightedFamily

/-! All weighted original native data are constructed from the actual parent
factory family. This removes the obsolete convex-domain input wrapper while
retaining every original native phase, reserve and support definition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
private local instance novClassFactoryChart : ChartedSpace X (P × M) := prodChartedSpace Ep P D M
private local instance novClassFactoryManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

namespace ClosureNovFixedClass.AllowedMap
variable {c : ClosureNovFixedClass m d N M P}

theorem weighted_exists {F0 : P × M → V} (h : c.AllowedMap F0) :
    ClosureNovWeightedFamilyResult c.numerical.referenceBudget c.numerical.Ds c.numerical.Dp
      (c.geometry.seed F0) h.sliceSmooth c.geometry.samples
      c.geometry.parentDomain c.geometry.parentCarrier (fun _ => 0) h.family
      (c.seedDomains F0) c.geometry.outer c.numerical.transition
      c.numerical.parameterTransition c.numerical.spatialTransition := by
  apply closureNov_original_weighted_family_realization c.numerical.referenceBudget
    c.numerical.Ds c.numerical.Dp (c.geometry.seed F0) h.sliceSmooth c.geometry.samples
    c.geometry.parentDomain c.geometry.parentCarrier (fun _ => 0) h.family
    (c.seedDomains F0) h.smooth c.geometry.samples_subset c.geometry.parentDomain_sample
    c.geometry.outer c.geometryBounds.parents.outer_smooth
    (fun p _ x => c.geometryBounds.parents.outer_partition (p,x)) c.geometry.outer_carrier
    c.geometry.source.support c.geometry.parameter.support
    c.geometryBounds.parents.source_degree c.geometryBounds.parents.parameter_degree
    c.geometryBounds.parents.outer_graph_support (fun _ => Subset.rfl)
    c.numerical.transition c.numerical.transition_pos.le
    c.numerical.parameterTransition c.numerical.spatialTransition c.numerical.spatial_first
  · intro i k j hj y hy ha
    exact (c.geometry.parameter_transition_jets i k j hj y hy ha).trans
      (c.geometryBounds.parameterTransition j)
  · intro i k j hj y hy ha
    exact (c.geometry.spatial_transition_jets i k j hj y hy ha).trans
      (c.geometryBounds.spatialTransition j)

end ClosureNovFixedClass.AllowedMap
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.ClosureNovFixedClass.AllowedMap.weighted_exists
