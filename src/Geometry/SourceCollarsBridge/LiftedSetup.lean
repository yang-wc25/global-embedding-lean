import SourceCollarsBridge.PrimitiveBudget
import Repair.SourceCollarNovGeometryBudget

/-!
# Fixed primitive budgets into the existing repair numerical class

The numerical input below has no manifold, atlas, prepared collar, or
reference map.  It bounds the original raw and transition data.  Enlarging
only the proofs of those bounds before calling the existing parent
producer makes its chosen scalar profiles literally the fixed profiles.
No monotonicity of a `Classical.choose` derivative constant is assumed.

`liftedSetup` retains the old `SourceCollarNovSetup` type, both atlases,
their supports and buffers, the norm domains, and all raw functions.  Its
actual parents, collars, samples and differentiation domains are equal to
the old ones.  `geometryBounds` is a direct constructor for the existing
`SourceCollarNovGeometryBounds`, using only primitive comparisons.

The old Setup still requires compact norm domains.  This module does not
claim to derive that premise; support compactness without that premise is
proved separately in `SourceCollarsBridge.CompactCarriers`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.SourceCollarsBridge

/-- Original numerical upper and lower bounds, chosen before every atlas. -/
structure PrimitiveGeometryBudget where
  BS : ℕ → ℝ
  TS : ℕ → ℝ
  BP : ℕ → ℝ
  TP : ℕ → ℝ
  parameterTransition : ℕ → ℝ
  spatialTransition : ℕ → ℝ
  BS_nonneg : ∀ j, 0 ≤ BS j
  TS_nonneg : ∀ j, 0 ≤ TS j
  BP_nonneg : ∀ j, 0 ≤ BP j
  TP_nonneg : ∀ j, 0 ≤ TP j
  parameter_nonneg : ∀ j, 0 ≤ parameterTransition j
  spatial_nonneg : ∀ j, 0 ≤ spatialTransition j
  Ds : ℕ
  Dp : ℕ
  coordinateRadius : ℝ
  coordinateRadius_nonneg : 0 ≤ coordinateRadius
  sourceBuffer : ℝ
  parameterBuffer : ℝ
  sourceBuffer_pos : 0 < sourceBuffer
  parameterBuffer_pos : 0 < parameterBuffer

namespace PrimitiveGeometryBudget
variable (b : PrimitiveGeometryBudget)

/-- The old numerical class with every derived parent profile and collar
radius manufactured from the fixed primitive bounds. -/
def numericalSetup {m d N : ℕ}
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
    modelRadius := b.coordinateRadius
    buffer := min (primitiveRadius b.sourceBuffer (b.BS 1))
      (primitiveRadius b.parameterBuffer (b.BP 1))
    mapC3_nonneg := hR 3
    tensorC1_nonneg := mul_nonneg (repairEntranceMetricCost_nonneg (m+1) d N 1) (sq_nonneg _)
    phaseMargin_pos := hMargin
    tensorLower_pos := hLower
    firstLower_pos := hLower
    buffer_pos := lt_min (primitiveRadius_pos b.sourceBuffer_pos (b.BS_nonneg 1))
      (primitiveRadius_pos b.parameterBuffer_pos (b.BP_nonneg 1))
    templateDim := by simpa using hDim
    ambientDim := hAmbient }
  mapBounds := R
  mapBounds_nonneg := hR
  BS := sourceCollarNovParentRawProfile b.BS
  TS := b.TS
  BP := sourceCollarNovParentRawProfile b.BP
  TP := b.TP
  parameterTransition := b.parameterTransition
  spatialTransition := b.spatialTransition
  BS_nonneg := sourceCollarNovParentRawProfile_nonneg b.BS b.BS_nonneg
  TS_nonneg := b.TS_nonneg
  BP_nonneg := sourceCollarNovParentRawProfile_nonneg b.BP b.BP_nonneg
  TP_nonneg := b.TP_nonneg
  parameter_nonneg := b.parameter_nonneg
  spatial_nonneg := b.spatial_nonneg
  Ds := b.Ds
  Dp := b.Dp
  transition := max 1 (b.spatialTransition 1)
  centerBound := 0
  parameterBound := b.coordinateRadius
  sourceBound := b.coordinateRadius
  lower := lower
  smoothingRadius := min b.parameterBuffer b.sourceBuffer
  transition_pos := zero_lt_one.trans_le (le_max_left _ _)
  centerBound_nonneg := le_rfl
  parameterBound_nonneg := b.coordinateRadius_nonneg
  sourceBound_nonneg := b.coordinateRadius_nonneg
  lower_pos := hLower
  smoothingRadius_pos := lt_min b.parameterBuffer_pos b.sourceBuffer_pos
  modelRadius_nonneg := b.coordinateRadius_nonneg
  spatial_first := le_max_right _ _
  mapC3 := le_rfl
  tensorC1 := le_rfl
  first_lower := le_rfl
  tensor_lower := le_rfl

end PrimitiveGeometryBudget

section General
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- Only primitive comparisons; there is no comparison of a generated
profile, no supplied parent, and no change to the source norm domain. -/
structure PrimitiveGeometryBounds
    (b : PrimitiveGeometryBudget) (g : SourceCollarNovSetup n d M P) : Prop where
  BS : ∀ j, g.BS j ≤ b.BS j
  TS : ∀ j, g.TS j ≤ b.TS j
  BP : ∀ j, g.BP j ≤ b.BP j
  TP : ∀ j, g.TP j ≤ b.TP j
  Ds : g.Ds ≤ b.Ds
  Dp : g.Dp ≤ b.Dp
  parameterTransition : ∀ j, g.parameterTransition j ≤ b.parameterTransition j
  spatialTransition : ∀ j, g.spatialTransition j ≤ b.spatialTransition j
  coordinateRadius : g.coordinateRadius ≤ b.coordinateRadius
  sourceBuffer : b.sourceBuffer ≤ g.source.buffer
  parameterBuffer : b.parameterBuffer ≤ g.parameter.buffer

namespace PrimitiveGeometryBounds
variable {b : PrimitiveGeometryBudget} {g : SourceCollarNovSetup n d M P}
  (h : PrimitiveGeometryBounds b g)

/-- Same old Setup type and all original functions; numerical proof
budgets alone are increased to the fixed primitive upper bounds. -/
def liftedSetup : SourceCollarNovSetup n d M P :=
  { g with
    BS := b.BS
    TS := b.TS
    BP := b.BP
    TP := b.TP
    BS_nonneg := b.BS_nonneg
    TS_nonneg := b.TS_nonneg
    BP_nonneg := b.BP_nonneg
    TP_nonneg := b.TP_nonneg
    Ds := b.Ds
    Dp := b.Dp
    sourcePreparation := rawPreparationWithBounds g.sourcePreparation h.BS h.TS h.Ds
    parameterPreparation := rawPreparationWithBounds g.parameterPreparation h.BP h.TP h.Dp
    coordinateRadius := b.coordinateRadius
    coordinateRadius_nonneg := b.coordinateRadius_nonneg
    source_bound := fun i x hx => (g.source_bound i x hx).trans h.coordinateRadius
    parameter_bound := fun i x hx => (g.parameter_bound i x hx).trans h.coordinateRadius
    parameterTransition := b.parameterTransition
    spatialTransition := b.spatialTransition
    parameterTransition_nonneg := b.parameter_nonneg
    spatialTransition_nonneg := b.spatial_nonneg
    parameter_transition_jets := fun ip jp k hk z hz hs =>
      (g.parameter_transition_jets ip jp k hk z hz hs).trans (h.parameterTransition k)
    spatial_transition_jets := fun i j k hk z hz hs =>
      (g.spatial_transition_jets i j k hk z hz hs).trans (h.spatialTransition k) }

/-- Exact preservation, not an identification with a replacement atlas. -/
theorem liftedSetup_original_geometry :
    h.liftedSetup.source = g.source ∧ h.liftedSetup.parameter = g.parameter ∧
    h.liftedSetup.Omega = g.Omega ∧ h.liftedSetup.Q = g.Q ∧
    h.liftedSetup.samples = g.samples ∧
    h.liftedSetup.differentiation = g.differentiation :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The raw and parent formulas do not depend on proof budgets. -/
theorem liftedSetup_original_functions :
    h.liftedSetup.sourcePreparation.raw = g.sourcePreparation.raw ∧
    h.liftedSetup.parameterPreparation.raw = g.parameterPreparation.raw ∧
    h.liftedSetup.sourceParentPreparation.raw = g.sourceParentPreparation.raw ∧
    h.liftedSetup.parameterParentPreparation.raw = g.parameterParentPreparation.raw ∧
    h.liftedSetup.outer = g.outer ∧ h.liftedSetup.theta = g.theta ∧
    h.liftedSetup.parentDomain = g.parentDomain ∧
    h.liftedSetup.parentCarrier = g.parentCarrier :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem liftedSetup_original_seed (F0 : P × M → EuclideanSpace ℝ (Fin N)) :
    h.liftedSetup.seed F0 = g.seed F0 := rfl

end PrimitiveGeometryBounds
end General

section RepairDimension
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

namespace PrimitiveGeometryBounds
variable {b : PrimitiveGeometryBudget} {g : SourceCollarNovSetup (m+1) d M P}
  (h : PrimitiveGeometryBounds b g)

/-- The existing geometry-bounds consumer now receives a proof built
entirely from original primitive bounds, without a generated-profile input. -/
theorem geometryBounds
    (R : ℕ → ℝ) (hR : ∀ j, 0 ≤ R j) (lower margin : ℝ)
    (hLower : 0 < lower) (hMargin : 0 < margin)
    (hDim : 2 ≤ m+1) (hAmbient : (m+1)*(m+2)/2 < N) :
    SourceCollarNovGeometryBounds
      (b.numericalSetup R hR lower margin hLower hMargin hDim hAmbient) h.liftedSetup where
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
  buffer := min_le_min
    (primitiveRadius_le_original g.source b.BS h.sourceBuffer (b.BS_nonneg 1) le_rfl)
    (primitiveRadius_le_original g.parameter b.BP h.parameterBuffer (b.BP_nonneg 1) le_rfl)
  smoothingRadius := min_le_min h.parameterBuffer h.sourceBuffer

include h in
/-- Direct connection to the old parent consumer, with its numerical class
fixed before the atlases and with the original outer and theta functions. -/
theorem parents
    (R : ℕ → ℝ) (hR : ∀ j, 0 ≤ R j) (lower margin : ℝ)
    (hLower : 0 < lower) (hMargin : 0 < margin)
    (hDim : 2 ≤ m+1) (hAmbient : (m+1)*(m+2)/2 < N) :
    let c := b.numericalSetup (d := d) R hR lower margin hLower hMargin hDim hAmbient
    RepairReferenceOriginalParentProperties g.source g.parameterFamily
      g.source.support g.parameter.support g.outer g.theta c.outerProfile c.parentProfile
      (fun j => max (c.TP j) (c.TS j)) c.Ds c.Dp :=
  (h.geometryBounds R hR lower margin hLower hMargin hDim hAmbient).parents

include h in
/-- The fixed numerical radius bounds a ball around the actual old
carrier inside the actual old parent domain. -/
theorem parent_buffer
    (R : ℕ → ℝ) (hR : ∀ j, 0 ≤ R j) (lower margin : ℝ)
    (hLower : 0 < lower) (hMargin : 0 < margin)
    (hDim : 2 ≤ m+1) (hAmbient : (m+1)*(m+2)/2 < N)
    (i) (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
    (hz : z ∈ g.parentCarrier i) :
    ball z (b.numericalSetup (d := d) R hR lower margin hLower hMargin hDim hAmbient).referenceBudget.buffer ⊆
      g.parentDomain i :=
  (h.geometryBounds R hR lower margin hLower hMargin hDim hAmbient).parent_buffer i z hz

end PrimitiveGeometryBounds
end RepairDimension
end GlobalEmbedding.Continuation.SourceCollarsBridge

#print axioms GlobalEmbedding.Continuation.SourceCollarsBridge.PrimitiveGeometryBudget.numericalSetup
#print axioms GlobalEmbedding.Continuation.SourceCollarsBridge.PrimitiveGeometryBounds.geometryBounds
#print axioms GlobalEmbedding.Continuation.SourceCollarsBridge.PrimitiveGeometryBounds.parents
#print axioms GlobalEmbedding.Continuation.SourceCollarsBridge.PrimitiveGeometryBounds.parent_buffer
