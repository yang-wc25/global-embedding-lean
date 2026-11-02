import RepairClosure.InterfaceCanonicalApplicationReference
import RepairClosure.UniformCoordinateRepair
import OriginalIntegration.CanonicalOriginalGeometry

/-!
# Original initialization uses the independently stated coordinate repair

The numerical phase convention proposed for uniform repair adds no input
assumption to this actual application. Both its finite reference core and
its positive coordinate margin are produced from `InitializationData`.
The source and parameter buffered geometry is the actual canonical one,
including its full original open norm domains.

The call to `uniform_coordinate_repair_complete` occurs before K, T, S.
Thus the actual growing chart counts and the limiting choice of frequency
cannot change the entrance epsilon. The conclusion explicitly retains the
manufactured inputs alongside the full original repair output.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Initialization
  Set Function Manifold IsManifold Bundle
open scoped ContDiff Topology

universe uM uP
namespace GlobalEmbedding.Continuation.RepairClosure
open OriginalIntegration

variable {m d : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
  [TopologicalSpace P] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin (closedAmbientDimension (m+1)))
local notation "I" => 𝓘(ℝ,Es)

attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
/-- A concrete consumer of the independently audited uniform coordinate
repair statement, with every one of its reference and geometry inputs
constructed from the original initialization. -/
theorem canonical_initialization_uniform_coordinate_repair
    [IsContinuousRiemannianBundle Es (TangentSpace I : M → Type _)]
    (data : InitializationData M m) (hm : 1 ≤ m)
    (metric0 : ContMDiffRiemannianMetric I ∞ Es (TangentSpace I : M → Type _))
    (GP : PreparedCharts P d) (rho : ℝ) (hrho : 0 < rho) :
    ∃ (B : InitializationReserves) (mu C : ℝ) (J : ℕ) (epsilon t0 : ℝ),
      ColoredApproximationCore data.charts metric0 data.frame data.phase.selector B ∧
      0 < mu ∧ 0 < C ∧ 442 ≤ J ∧
      0 < epsilon ∧ 0 < t0 ∧ t0 < 1 ∧
      (∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
        B.K₀ ≤ K → B.R₀*K ≤ T → ∀ x : M,
        T^2*mu ≤ truePhaseMargin
          (metricInitializationMap data.charts metric0 data.frame data.phase.selector K T hK)
          (data.map_smooth metric0 K T hK) x) ∧
      (∀ (K T S : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T) (hS : 1 ≤ S),
        B.K₀ ≤ K → B.R₀*K ≤ T →
        let g := canonicalOriginalGeometry data.charts GP T S (hK.trans hKT) hS
        let F0 : P × M → V := fun px =>
          metricInitializationMap data.charts metric0 data.frame data.phase.selector K T hK px.2
        RepairReferenceCore g (canonicalRepairReferenceProfile (m+1) d B)
          B.mapLower J F0 ∧
        CoordinateReferencePhase g (mu/C) F0 ∧
        RepairForEveryOriginalMetric g F0 rho epsilon t0) := by
  obtain ⟨B,mu,C,hB,hmu,hC,hNative,hReference⟩ :=
    InitializationData.exists_independent_coordinate_references.{uM,uP} data hm metric0
  have hAmbient : (m+1)*(m+2)/2 < closedAmbientDimension (m+1) := by
    simp only [closedAmbientDimension, symmetricTensorDimension]
    rw [show m+1+1 = m+2 by omega]
    exact Nat.lt_succ_self _
  obtain ⟨J,epsilon,t0,h442,he,ht,h1,hRepair⟩ :=
    uniform_coordinate_repair_complete.{uM,uP} (m := m) (d := d)
      (N := closedAmbientDimension (m+1)) M
      (canonicalOriginalGeometryBudget data.charts GP)
      (canonicalRepairReferenceProfile (m+1) d B)
      (canonicalRepairReferenceProfile_nonneg (m+1) d B)
      B.mapLower (mu/C) B.mapLower_pos (div_pos hmu hC)
      (by omega) hAmbient rho hrho
  refine ⟨B,mu,C,J,epsilon,t0,hB,hmu,hC,h442,he,ht,h1,hNative,?_⟩
  intro K T S hK hKT hS hK0 hR0
  let g := canonicalOriginalGeometry data.charts GP T S (hK.trans hKT) hS
  let F0 : P × M → V := fun px =>
    metricInitializationMap data.charts metric0 data.frame data.phase.selector K T hK px.2
  obtain ⟨hCore,hPhase⟩ := hReference K T hK hKT hK0 hR0 d
    (canonicalOriginalGeometryBudget data.charts GP) P g rfl J
  exact ⟨hCore,hPhase,hRepair P g F0 hCore hPhase⟩

end GlobalEmbedding.Continuation.RepairClosure

#print axioms GlobalEmbedding.Continuation.RepairClosure.canonical_initialization_uniform_coordinate_repair
