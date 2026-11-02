import OriginalIntegration.CanonicalAtlasGeometry

/-!
# Actual two-scale original repair geometry, entirely manufactured

The numerical budget is fixed from two prepared compact parent atlases.
Both scale parameters and both actual chart counts occur afterwards.
The resulting original norm domains are the full open targets of the
actual initialization atlases; the supports are the original enlarged
supports. Every field is obtained from the genuine atlas construction.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Initialization
  Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.OriginalIntegration

variable {n d : ℕ} {M P : Type*}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [TopologicalSpace P] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

def canonicalOriginalGeometryBudget (GM : PreparedCharts M n) (GP : PreparedCharts P d) :
    OriginalRepairGeometryBudget where
  sourceRadius := GM.scaleRadius
  sourceBuffer := GM.scaleRadius/10
  parameterRadius := GP.scaleRadius
  parameterBuffer := GP.scaleRadius/10
  sourceBuffer_pos := div_pos GM.scaleRadius_pos (by norm_num)
  parameterBuffer_pos := div_pos GP.scaleRadius_pos (by norm_num)
  sourceRawTransition := originalCanonicalTransitionProfile GM
  parameterRawTransition := originalCanonicalTransitionProfile GP
  parameterTransition := fun j => max (originalCanonicalTransitionProfile GP j) 1
  spatialTransition := fun j => max 1 (originalCanonicalTransitionProfile GM j)
  sourceRawTransition_nonneg := fun j => (originalCanonicalTransitionProfile_pos GM j).le
  parameterRawTransition_nonneg := fun j => (originalCanonicalTransitionProfile_pos GP j).le
  parameterTransition_nonneg := fun j => zero_le_one.trans (le_max_right _ _)
  spatialTransition_nonneg := fun j => zero_le_one.trans (le_max_left _ _)
  sourceDegree := originalCanonicalSupportDegree GM
  parameterDegree := originalCanonicalSupportDegree GP

/-- No geometry is supplied here: this is the original actual scale-atlas
pair, with each required field proved from the two fixed preparations. -/
def canonicalOriginalGeometry
    (GM : PreparedCharts M n) (GP : PreparedCharts P d)
    (T S : ℝ) (hT : 1 ≤ T) (hS : 1 ≤ S) :
    OriginalRepairGeometry (canonicalOriginalGeometryBudget GM GP) n d M P where
  atlas := initializationAtlas GM T hT
  Omega := fun i => ((initializationAtlas GM T hT).chart i).target
  parameterCount := (initializationAtlas GP S hS).count
  parameterChart := (initializationAtlas GP S hS).chart
  Q := fun i => ((initializationAtlas GP S hS).chart i).target
  parameterSupport := (initializationAtlas GP S hS).support
  sourceBuffer := originalCanonicalAtlas_norm_buffer GM T hT
  parameterBuffer := originalCanonicalAtlas_parameter_buffer GP S hS
  atlas_smooth := originalCanonicalAtlas_smooth GM T hT
  parameter_smooth := (originalCanonicalAtlas_smooth GP S hS).chart_mem
  source_degree := originalCanonicalSupportDegree_bound GM T hT
  parameter_degree := fun i => (tensorSupportDegree_le_original
    (initializationAtlas GP S hS) i).trans (originalCanonicalSupportDegree_bound GP S hS)
  source_raw_transition := originalCanonicalAtlas_raw_transition GM T hT
  parameter_raw_transition := fun p i j hj y hy hi _ =>
    originalCanonicalAtlas_raw_transition GP S hS p i j hj y hy hi
  parameter_transition := originalCanonicalAtlas_parameter_joint GP S hS
  spatial_transition := originalCanonicalAtlas_spatial_joint GM T hT

theorem canonicalOriginalGeometry_fields
    (GM : PreparedCharts M n) (GP : PreparedCharts P d)
    (T S : ℝ) (hT : 1 ≤ T) (hS : 1 ≤ S) :
    (canonicalOriginalGeometry GM GP T S hT hS).atlas = initializationAtlas GM T hT ∧
    (canonicalOriginalGeometry GM GP T S hT hS).parameterChart =
      (initializationAtlas GP S hS).chart ∧
    (∀ i, (canonicalOriginalGeometry GM GP T S hT hS).Omega i =
      ((initializationAtlas GM T hT).chart i).target) ∧
    (∀ i, (canonicalOriginalGeometry GM GP T S hT hS).Q i =
      ((initializationAtlas GP S hS).chart i).target) :=
  ⟨rfl,rfl,fun _ => rfl,fun _ => rfl⟩

end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.canonicalOriginalGeometryBudget
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.canonicalOriginalGeometry
