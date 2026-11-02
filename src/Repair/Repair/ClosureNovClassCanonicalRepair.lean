import Repair.ClosureNovClassSmoothing
import Repair.EntranceCanonicalActualFactory
import Repair.EntranceCanonicalNativePhaseRegular

/-! The actual weighted datum, including all native phase and positive
reserve certificates, selected from the proved original-map producer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace M] [CompactSpace P]
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

/-- The original finite entrance assumptions now construct the complete
actual increment and the single smooth exact-metric repair trajectory.
There is no family, solver, output estimate or initialized-state premise. -/
theorem canonical_actual_planned_limit {F0 : P × M → V}
    (h : c.AllowedMap F0) (rho : ℝ) (hrho : 0 < rho) :
    RepairEntranceCanonicalNativePlannedLimit (h.data) (h.smoothing)
      (c.numerical.parameters rho hrho) c.numerical.plan (c.numerical.mapBounds 2) (c.numerical.mapBounds 442) rho := by
  have hn := h.native_properties
  have hc := h.completed_prefix_and_envelope
  have hRun : RepairEntranceCanonicalPlannedLimit (h.data) (h.smoothing)
      (c.numerical.parameters rho hrho) c.numerical.plan (c.numerical.mapBounds 2) (c.numerical.mapBounds 442) rho :=
    repairEntranceCanonical_actual_factory_planned_repair c.numerical.referenceBudget
      c.numerical.transition c.numerical.centerBound c.numerical.parameterBound c.numerical.sourceBound c.numerical.lower c.numerical.rawReserve c.numerical.reserve
      (c.numerical.mapBounds 2) (c.numerical.mapBounds 442) rho c.numerical.labelBound c.numerical.Ds c.numerical.Dp c.numerical.labelBound
      c.numerical.smoothingRadius c.numerical.smoothingRadius_pos c.numerical.BS c.numerical.TS c.numerical.BP c.numerical.TP c.numerical.parentProfile
      c.numerical.parameterTransition c.numerical.spatialTransition c.numerical.givenProfile c.numerical.referenceProfile c.numerical.referenceProfile
      c.numerical.BS_nonneg c.numerical.TS_nonneg c.numerical.BP_nonneg c.numerical.TP_nonneg c.numerical.parentProfile_nonneg
      c.numerical.parameter_nonneg c.numerical.spatial_nonneg c.numerical.referenceProfile_nonneg c.numerical.referenceProfile_nonneg
      c.numerical.transition_pos c.numerical.centerBound_nonneg c.numerical.parameterBound_nonneg c.numerical.sourceBound_nonneg
      c.numerical.modelRadius_nonneg c.numerical.lower_pos c.numerical.reserve_pos (c.numerical.mapBounds_nonneg 2) (c.numerical.mapBounds_nonneg 442)
      hrho c.numerical.spatial_first
      (c.geometry.seed F0) h.sliceSmooth (fun p x => inducedMetric (I := 𝓘(ℝ,D)) (fun y => F0 (p,y)) x)
      c.geometry.samples c.geometry.parentDomain c.geometry.parentCarrier (fun _ => 0)
      (h.family) (c.seedDomains F0) c.geometry.samples_subset c.geometry.parentDomain_sample
      (fun _ => Subset.rfl) c.geometry.parentDomain_open c.geometryBounds.parentCarrier_bound c.geometryBounds.parent_buffer
      (fun i z hz => (c.geometry.parentDomain_inner i z hz).2)
      (fun _ => by simpa using c.numerical.centerBound_nonneg)
      (fun i p hp => (c.geometry.parameter_bound i p hp).trans c.geometryBounds.parameterBound)
      (fun i x hx => (c.geometry.source_bound i x hx).trans c.geometryBounds.sourceBound)
      c.geometry.outer (h.label) (fun nu => (h.label_lt nu).le) (h.label_proper)
      (h.completedProfiles).reference (h.completedProfiles).Given (h.completedProfiles).metricReference
      (h.smoothing) rfl rfl rfl rfl (h.nativeSmooth) hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.2.1
      hn.2.2.2.2.2.1 (h.immersion) (h.ellipticity_inputs) hn.2.2.2.1 hn.2.2.2.2.2.2
      (h.map_bounds 2 (by decide)) (h.map_bounds 442 (by decide)) hc.2
      hc.1.Given hc.1.reference hc.1.metricReference
      c.geometryBounds.parents.theta_compact c.geometryBounds.parents.theta_smooth c.geometry.theta_carrier
      c.geometryBounds.parents.theta_partition c.geometryBounds.parents.theta_count
      (fun parent i j z hz => c.geometryBounds.parents.theta_original_jets c.geometry.Omega c.geometry.Q univ i parent j z hz)
  exact hRun.native rfl rfl hn.2.2.1 (h.immersion)

end ClosureNovFixedClass.AllowedMap
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.ClosureNovFixedClass.AllowedMap.canonical_actual_planned_limit
