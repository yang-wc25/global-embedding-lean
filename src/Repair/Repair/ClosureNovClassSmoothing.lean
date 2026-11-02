import Repair.ClosureNovClassNative
import Repair.EndpointFiniteSmoothingRealization

/-! The actual weighted datum, including all native phase and positive
reserve certificates, selected from the proved original-map producer. -/
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
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
private local instance : ChartedSpace X (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

namespace ClosureNovFixedClass.AllowedMap
variable {c : ClosureNovFixedClass m d N M P}

theorem original_transitions {F0 : P × M → V}
    (h : c.AllowedMap F0) :
    RepairOriginalTransitionBudgets (h.raw) c.numerical.parameterTransition c.numerical.spatialTransition where
  parameter := fun ip jp k hk z hz ho =>
    (c.geometry.parameter_transition_jets ip jp k hk z hz ho).trans (c.geometryBounds.parameterTransition k)
  spatial := fun i j k hk z hz ho =>
    (c.geometry.spatial_transition_jets i j k hk z hz ho).trans (c.geometryBounds.spatialTransition k)

theorem fixed_budget {F0 : P × M → V}
    (h : c.AllowedMap F0) (j : ℕ) :
    parameterRound2_originalFixedPacketProfile (h.data) j 1 ≠ ⊤ ∧
    (j ≤ repairEntrancePrimitiveDepth →
      (parameterRound2_originalFixedPacketProfile (h.data) j 1).toReal ≤ c.numerical.givenProfile j) := by
  exact repair_reference_actual_factory_finite_fixed_budget c.numerical.referenceBudget (c.geometry.seed F0) h.sliceSmooth
    (fun p x => inducedMetric (I := 𝓘(ℝ,D)) (fun y => F0 (p,y)) x) c.geometry.samples
    c.geometry.parentDomain c.geometry.parentCarrier (fun _ => 0) (h.family)
    (c.seedDomains F0) h.smooth rfl c.geometry.samples_subset c.geometry.parentDomain_sample
    (fun _ => Subset.rfl) c.geometry.outer c.geometryBounds.parents.outer_smooth c.geometryBounds.parents.outer_source
    repairEntrancePrimitiveDepth c.numerical.mapBounds c.numerical.outerProfile c.numerical.parameterTransition c.numerical.spatialTransition
    c.numerical.mapBounds_nonneg c.numerical.outerProfile_nonneg c.numerical.parameter_nonneg c.numerical.spatial_nonneg c.geometry.samples_compact
    (fun k hk => h.map_bounds k hk) c.numerical.sourceBound c.numerical.sourceBound_nonneg
    (fun i x hx => (c.geometry.source_bound i x hx).trans c.geometryBounds.sourceBound)
    (fun owner i k y hy => c.geometryBounds.parents.outer_original_jets c.geometry.Omega c.geometry.Q univ i owner k y hy)
    c.numerical.rawReserve c.numerical.transition c.numerical.transition_pos.le c.numerical.labelBound (h.label)
    (fun nu => (h.label_lt nu).le) (h.original_transitions) j

def smoothingGeometry {F0 : P × M → V} (h : c.AllowedMap F0) :
    RepairOriginalSmoothingGeometry h.data c.numerical.BS c.numerical.TS c.numerical.BP c.numerical.TP
      c.numerical.Ds c.numerical.Dp c.numerical.smoothingRadius :=
  c.geometryBounds.smoothingGeometry h.data rfl rfl HEq.rfl HEq.rfl HEq.rfl rfl

def baseSmoothing {F0 : P × M → V}
    (h : c.AllowedMap F0) :=
  repair_original_actual_smoothing_packet (h.data) (h.domain) (h.nativeSmooth) rfl rfl
    c.numerical.BS c.numerical.TS c.numerical.BP c.numerical.TP c.numerical.Ds c.numerical.Dp c.numerical.smoothingRadius c.numerical.smoothingRadius_pos (h.smoothingGeometry)
    rfl rfl (fun j => (h.fixed_budget j).1)

theorem base_samples {F0 : P × M → V}
    (h : c.AllowedMap F0) : (h.baseSmoothing).closedSamples=c.geometry.samples := rfl

def completedProfiles {F0 : P × M → V}
    (h : c.AllowedMap F0) : RepairEntranceProfiles :=
  repairEntranceOriginalClassProfiles c.numerical.plan repairEntrancePrimitiveDepth (h.baseSmoothing)

def smoothing {F0 : P × M → V}
    (h : c.AllowedMap F0) :=
  repairEntranceOriginalClassPacket c.numerical.plan repairEntrancePrimitiveDepth c.numerical.mapBounds
    (fun j _ => c.numerical.mapBounds_nonneg j) (fun _ _ => rfl) (h.baseSmoothing) rfl rfl rfl
    (fun j hj => h.map_bounds j hj) (fun j hj => (h.fixed_budget j).2 hj)

theorem completed_prefix_and_envelope {F0 : P × M → V}
    (h : c.AllowedMap F0) :
    c.numerical.plan.Prefix (h.completedProfiles) repairEntrancePrimitiveDepth ∧
    (∀ j, (h.smoothing).closedReferenceProfile j ≤ (h.completedProfiles).metricReference j) := by
  have hAll := repairEntranceOriginalClassPacket_prefix_and_envelope c.numerical.plan repairEntrancePrimitiveDepth
    c.numerical.mapBounds (fun j _ => c.numerical.mapBounds_nonneg j) (fun _ _ => rfl) rfl
    (h.baseSmoothing) rfl rfl rfl (fun j hj => h.map_bounds j hj)
    (fun j hj => (h.fixed_budget j).2 hj)
  exact ⟨hAll.1,hAll.2.1⟩

end ClosureNovFixedClass.AllowedMap
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.ClosureNovFixedClass.AllowedMap.fixed_budget
#print axioms GlobalEmbedding.Continuation.ClosureNovFixedClass.AllowedMap.completed_prefix_and_envelope
