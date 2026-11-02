import FaithfulCollars.OverlapOnlyRawSupply
import OriginalIntegration.OriginalRepairOutput

/-!
# Primitive original geometry at the repair entrance

This record spells out the buffered-radius and transition part of
`setup:uniform`.  Its numerical budget is fixed before any atlas count.
Its actual geometry has no raw functions, prepared collars, inverse
suppliers, smoothing packet, output map or requested estimate as a field.
The genuine norm-buffer relations correct the bare atlas interface, whose
independent `support` and norm-domain fields did not express subordination.

The internal compact Setup is a proved output.  Its original chart maps
and carrier inclusions are retained explicitly for the final norm return.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.OriginalIntegration
open FaithfulCollars SourceCollarsBridge

structure OriginalRepairGeometryBudget where
  sourceRadius : ℝ
  sourceBuffer : ℝ
  parameterRadius : ℝ
  parameterBuffer : ℝ
  sourceBuffer_pos : 0 < sourceBuffer
  parameterBuffer_pos : 0 < parameterBuffer
  sourceRawTransition : ℕ → ℝ
  parameterRawTransition : ℕ → ℝ
  parameterTransition : ℕ → ℝ
  spatialTransition : ℕ → ℝ
  sourceRawTransition_nonneg : ∀ j, 0 ≤ sourceRawTransition j
  parameterRawTransition_nonneg : ∀ j, 0 ≤ parameterRawTransition j
  parameterTransition_nonneg : ∀ j, 0 ≤ parameterTransition j
  spatialTransition_nonneg : ∀ j, 0 ≤ spatialTransition j
  sourceDegree : ℕ
  parameterDegree : ℕ

def OriginalRepairGeometryBudget.primitive (b : OriginalRepairGeometryBudget) (n d : ℕ) :
    PrimitiveGeometryBudget :=
  fixedOriginalPrimitiveGeometryBudget n d b.sourceRadius b.sourceBuffer
    b.parameterRadius b.parameterBuffer b.sourceBuffer_pos b.parameterBuffer_pos
    b.sourceRawTransition b.parameterRawTransition b.parameterTransition b.spatialTransition
    b.sourceRawTransition_nonneg b.parameterRawTransition_nonneg
    b.parameterTransition_nonneg b.spatialTransition_nonneg b.sourceDegree b.parameterDegree

structure OriginalRepairGeometry (b : OriginalRepairGeometryBudget) (n d : ℕ) (M P : Type*)
    [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] where
  atlas : BufferedAtlas M (EuclideanSpace ℝ (Fin n))
  Omega : Fin atlas.count → Set (EuclideanSpace ℝ (Fin n))
  parameterCount : ℕ
  parameterChart : Fin parameterCount → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d))
  Q : Fin parameterCount → Set (EuclideanSpace ℝ (Fin d))
  parameterSupport : Fin parameterCount → Set P
  sourceBuffer : OriginalSourceNormBuffer atlas Omega b.sourceRadius b.sourceBuffer
  parameterBuffer : OriginalParameterNormBuffer parameterChart Q parameterSupport univ
    b.parameterRadius b.parameterBuffer
  atlas_smooth : IsSmoothBufferedAtlas atlas
  parameter_smooth : ∀ i, parameterChart i ∈ maximalAtlas 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P
  source_degree : atlas.supportDegree ≤ b.sourceDegree
  parameter_degree : ∀ i, tensorEnlargedSupportDegree parameterSupport i ≤ b.parameterDegree
  source_raw_transition : ∀ p i j, 1 ≤ j → ∀ y ∈ (atlas.chart p).target,
    (atlas.chart p).symm y ∈ atlas.support i →
    ‖iteratedFDeriv ℝ j (atlas.chart i ∘ (atlas.chart p).symm) y‖ ≤ b.sourceRawTransition j
  parameter_raw_transition : ∀ p i j, 1 ≤ j → ∀ y ∈ (parameterChart p).target,
    (parameterChart p).symm y ∈ parameterSupport i →
    (parameterChart p).symm y ∈ (parameterChart i).source →
    ‖iteratedFDeriv ℝ j (parameterChart i ∘ (parameterChart p).symm) y‖ ≤ b.parameterRawTransition j
  parameter_transition : OriginalParameterJointTransitions (n := n) parameterChart Q b.parameterTransition
  spatial_transition : OriginalSpatialJointTransitions (d := d) atlas Omega b.spatialTransition

namespace OriginalRepairGeometry
variable {b : OriginalRepairGeometryBudget} {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

def seed (g : OriginalRepairGeometry b n d M P) (F0 : P × M → EuclideanSpace ℝ (Fin N)) :
    RepairOriginalReferenceSeed n d N M P where
  atlas := g.atlas
  sourceNormDomain := g.Omega
  parameterCount := g.parameterCount
  parameterChart := g.parameterChart
  parameterNormDomain := g.Q
  parameterSet := univ
  parameterOpen := univ
  F0 := F0

def samples (g : OriginalRepairGeometry b n d M P) :=
  incrementsOriginalEvaluation g.atlas g.parameterChart g.Omega g.Q univ

def differentiation (g : OriginalRepairGeometry b n d M P) :=
  incrementsOriginalDifferentiation g.atlas g.parameterChart

/-- All old geometric packages are manufactured, with the exact original
chart identities available to the final native output transport. -/
theorem actual_compact_supply [T2Space M] [T2Space P]
    (g : OriginalRepairGeometry b n d M P) :
    ∃ c : SourceCollarNovSetup n d M P,
      ∃ hs : c.source.count = g.atlas.count,
        ∃ hp : c.parameter.count = g.parameterCount,
        (∀ i, c.source.chart i = g.atlas.chart (Fin.cast hs i)) ∧
        (∀ i, c.parameter.chart i = g.parameterChart (Fin.cast hp i)) ∧
        (∀ i, c.source.support i = g.atlas.support (Fin.cast hs i)) ∧
        (∀ i, c.parameter.support i ⊆ g.parameterSupport (Fin.cast hp i)) ∧
        (∀ i, c.Omega i ⊆ g.Omega (Fin.cast hs i)) ∧
        (∀ i, c.Q i ⊆ g.Q (Fin.cast hp i)) ∧
        c.source.buffer = (b.primitive n d).sourceBuffer ∧
        c.parameter.buffer = (b.primitive n d).parameterBuffer ∧
        PrimitiveGeometryBounds (b.primitive n d) c :=
  fixedOriginalPrimitiveGeometryBudget_supply_on_overlaps n d b.sourceRadius b.sourceBuffer
    b.parameterRadius b.parameterBuffer b.sourceBuffer_pos b.parameterBuffer_pos
    b.sourceRawTransition b.parameterRawTransition b.parameterTransition b.spatialTransition
    b.sourceRawTransition_nonneg b.parameterRawTransition_nonneg
    b.parameterTransition_nonneg b.spatialTransition_nonneg b.sourceDegree b.parameterDegree
    M P g.atlas g.Omega g.sourceBuffer g.parameterCount g.parameterChart g.Q g.parameterSupport
    g.parameterBuffer g.atlas_smooth g.parameter_smooth g.source_degree g.parameter_degree
    g.source_raw_transition g.parameter_raw_transition g.parameter_transition g.spatial_transition

end OriginalRepairGeometry
end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.OriginalRepairGeometry.actual_compact_supply
