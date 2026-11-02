import Repair.SourceCollarNovSetup
import Repair.EndpointOriginalNumericalSetup
import Repair.SourceCollarNovGeometryBudget

/-!
# Numerical repair data from the original buffered Setup

All choices here precede the reference map and target metric.  The old
numerical setup is retained.  The actual auxiliary cutoff profiles, source
and parameter buffers, original radius, and original sampled transition
profiles supply its fields; no completed collar is read.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

namespace SourceCollarNovSetup

/-- The old numerical contract, actually produced from the original data.
Its formula never reads an atlas count. -/
def numericalSetup (g : SourceCollarNovSetup (m+1) d M P)
    (R : ℕ → ℝ) (hR : ∀ j, 0 ≤ R j) (lower margin : ℝ)
    (hLower : 0 < lower) (hMargin : 0 < margin)
    (hDim : 2 ≤ m+1) (hAmbient : (m+1)*(m+2)/2 < N) :
    RepairOriginalNumericalSetup m d N where
  referenceBudget := {
    mapC3 := R 3
    tensorC1 := repairEntranceMetricCost (m+1) d N 1*(R 3)^2
    phaseMargin := margin
    tensorLower := lower
    firstLower := lower
    modelRadius := g.coordinateRadius
    buffer := min (sourceCollarNovParentRadius g.source g.BS)
      (sourceCollarNovParentRadius g.parameter g.BP)
    mapC3_nonneg := hR 3
    tensorC1_nonneg := mul_nonneg (repairEntranceMetricCost_nonneg (m+1) d N 1) (sq_nonneg _)
    phaseMargin_pos := hMargin
    tensorLower_pos := hLower
    firstLower_pos := hLower
    buffer_pos := lt_min (sourceCollarNovParentRadius_pos g.source g.BS (g.BS_nonneg 1))
      (sourceCollarNovParentRadius_pos g.parameter g.BP (g.BP_nonneg 1))
    templateDim := by simpa using hDim
    ambientDim := hAmbient }
  mapBounds := R
  mapBounds_nonneg := hR
  BS := sourceCollarNovParentRawProfile g.BS
  TS := g.TS
  BP := sourceCollarNovParentRawProfile g.BP
  TP := g.TP
  parameterTransition := g.parameterTransition
  spatialTransition := g.spatialTransition
  BS_nonneg := g.sourceParentProfile_nonneg
  TS_nonneg := g.TS_nonneg
  BP_nonneg := g.parameterParentProfile_nonneg
  TP_nonneg := g.TP_nonneg
  parameter_nonneg := g.parameterTransition_nonneg
  spatial_nonneg := g.spatialTransition_nonneg
  Ds := g.Ds
  Dp := g.Dp
  transition := max 1 (g.spatialTransition 1)
  centerBound := 0
  parameterBound := g.coordinateRadius
  sourceBound := g.coordinateRadius
  lower := lower
  smoothingRadius := min g.parameter.buffer g.source.buffer
  transition_pos := zero_lt_one.trans_le (le_max_left _ _)
  centerBound_nonneg := le_rfl
  parameterBound_nonneg := g.coordinateRadius_nonneg
  sourceBound_nonneg := g.coordinateRadius_nonneg
  lower_pos := hLower
  smoothingRadius_pos := lt_min g.parameter.buffer_pos g.source.buffer_pos
  modelRadius_nonneg := g.coordinateRadius_nonneg
  spatial_first := le_max_right _ _
  mapC3 := le_rfl
  tensorC1 := le_rfl
  first_lower := le_rfl
  tensor_lower := le_rfl

/-- The canonical numerical class satisfies every primitive comparison.
The statement also permits a fixed, larger numerical class before choosing
any original atlas. -/
theorem numericalSetup_bounds (g : SourceCollarNovSetup (m+1) d M P)
    (R : ℕ → ℝ) (hR : ∀ j, 0 ≤ R j) (lower margin : ℝ)
    (hLower : 0 < lower) (hMargin : 0 < margin)
    (hDim : 2 ≤ m+1) (hAmbient : (m+1)*(m+2)/2 < N) :
    SourceCollarNovGeometryBounds
      (g.numericalSetup R hR lower margin hLower hMargin hDim hAmbient) g where
  BS := fun _ => le_rfl
  TS := fun _ => le_rfl
  BP := fun _ => le_rfl
  TP := fun _ => le_rfl
  Ds := le_rfl
  Dp := le_rfl
  parameterTransition := fun _ => le_rfl
  spatialTransition := fun _ => le_rfl
  sourceBound := le_rfl
  parameterBound := le_rfl
  modelRadius := le_rfl
  buffer := le_rfl
  smoothingRadius := le_rfl

end SourceCollarNovSetup
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.SourceCollarNovSetup.numericalSetup
