import Repair.ClosureNovSetupNumerical
import Repair.ClosureNovSetupEllipticity
import Repair.ClosureNovGeneralParentFactory
import Repair.SourceCollarNovGeometryBudget

/-!
# The original fixed input class constructs the nonconvex source factories

This bundle contains only original fixed Setup data and numerical reference
bounds.  Its numerical setup and every actual local factory are definitions
with proved bodies.  No collar, normal, decomposition, completed packet or
repair output is stored in the input class.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle
open scoped ContDiff Topology TensorProduct ENNReal BigOperators
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance novClassRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance novClassSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

structure ClosureNovFixedClass (m d N : ℕ) (M P : Type*)
    [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] where
  numerical : RepairOriginalNumericalSetup m d N
  geometry : SourceCollarNovSetup (m+1) d M P
  geometryBounds : SourceCollarNovGeometryBounds numerical geometry

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
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
private local instance novClassProductChart : ChartedSpace X (P × M) := prodChartedSpace Ep P D M
private local instance novClassProductManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

namespace ClosureNovFixedClass

abbrev mapBounds (c : ClosureNovFixedClass m d N M P) := c.numerical.mapBounds
abbrev lower (c : ClosureNovFixedClass m d N M P) := c.numerical.lower
abbrev margin (c : ClosureNovFixedClass m d N M P) := c.numerical.referenceBudget.phaseMargin
theorem mapBounds_nonneg (c : ClosureNovFixedClass m d N M P) (j : ℕ) :
    0 ≤ c.mapBounds j := c.numerical.mapBounds_nonneg j
theorem lower_pos (c : ClosureNovFixedClass m d N M P) : 0 < c.lower := c.numerical.lower_pos
theorem margin_pos (c : ClosureNovFixedClass m d N M P) : 0 < c.margin :=
  c.numerical.referenceBudget.phaseMargin_pos
theorem sourceDim (c : ClosureNovFixedClass m d N M P) : 2 ≤ m+1 := by
  simpa using c.numerical.referenceBudget.templateDim
theorem ambientDim (c : ClosureNovFixedClass m d N M P) : (m+1)*(m+2)/2 < N :=
  c.numerical.referenceBudget.ambientDim

/-- Exactly the original finite map norms and spatial low margins. -/
structure AllowedMap (c : ClosureNovFixedClass m d N M P) (F0 : P × M → EuclideanSpace ℝ (Fin N)) : Prop where
  smooth : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F0
  map_bounds : ∀ j, j ≤ repairEntranceOriginalMapDepth →
    (paperAtlasCj j (incrementsOriginalMapCoordinates c.geometry.source c.geometry.parameter.chart F0)
      c.geometry.differentiation c.geometry.samples).toReal ≤ c.mapBounds j
  ellipticity : ∀ p i y, y ∈ c.geometry.Omega i → ∀ v : D,
    c.lower*‖v‖^2 ≤ ‖fderiv ℝ (fun x => F0 (p,(c.geometry.source.chart i).symm x)) y v‖^2
  phase_margin : ∀ i z, parameterTensorModelEquiv (m+1) d z ∈ c.geometry.samples i →
    c.margin ≤ bestPhaseSupremum
      (repairReferenceFactoryField (c.geometry.seed F0)
        (fun p x => inducedMetric (I := 𝓘(ℝ,D)) (fun y => F0 (p,y)) x) i z).1

theorem seedDomains [CompactSpace P] (c : ClosureNovFixedClass m d N M P) (F0 : P × M → EuclideanSpace ℝ (Fin N)) :
    RepairReferenceSeedDomains (c.geometry.seed F0) :=
  c.geometry.seed_domains c.sourceDim
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using Nat.succ_le_of_lt c.ambientDim) F0

namespace AllowedMap
variable {c : ClosureNovFixedClass m d N M P} {F0 : P × M → EuclideanSpace ℝ (Fin N)}

theorem sliceSmooth (h : c.AllowedMap F0) (p : P) :
    ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (fun x => F0 (p,x)) :=
  parameterRound2_native_source_slice_contMDiff h.smooth p

theorem map3_original_bound (h : c.AllowedMap F0) :
    paperAtlasCj 3 (incrementsOriginalMapCoordinates c.geometry.source c.geometry.parameter.chart F0)
      c.geometry.differentiation c.geometry.samples ≤ ENNReal.ofReal (c.mapBounds 3) := by
  have hSmooth := parameterRound2_originalMapCoordinates_contDiffOn
    c.geometry.source c.geometry.parameter.chart c.geometry.source_smooth
    c.geometry.parameter_smooth.chart_mem F0 h.smooth
  have hFinite := parameterRound2_paperAtlasCj_finite_of_compact _ _ c.geometry.samples
    (parameterRound2_originalDifferentiation_open c.geometry.source c.geometry.parameter.chart)
    c.geometry.samples_compact c.geometry.samples_subset hSmooth 3
  exact (ENNReal.ofReal_toReal hFinite).symm.le.trans
    (ENNReal.ofReal_le_ofReal (h.map_bounds 3 (by decide)))

theorem map3_bound (h : c.AllowedMap F0) :
    paperAtlasCj 3 (incrementsOriginalMapCoordinates c.geometry.source c.geometry.parameter.chart F0)
      c.geometry.differentiation c.geometry.samples ≤ ENNReal.ofReal c.numerical.referenceBudget.mapC3 :=
  h.map3_original_bound.trans (ENNReal.ofReal_le_ofReal c.numerical.mapC3)

/-- Every genuine factory is produced on the actual inner parent collar.
The original charts and norm domains are definitionally the seed fields. -/
def family (h : c.AllowedMap F0)
    (i : Fin c.geometry.source.count × Fin c.geometry.parameter.count) :
    RepairReferenceOriginalLocalFactory c.numerical.referenceBudget
      (c.geometry.seed F0) h.sliceSmooth
      (fun p x => inducedMetric (I := 𝓘(ℝ,D)) (fun y => F0 (p,y)) x) c.geometry.samples i
      (c.geometry.parentDomain i) (c.geometry.parentCarrier i) 0 := by
  have hMap3 := map3_original_bound (F0 := F0) h
  have hEll := closureNov_reference_joint_ellipticity c.geometry F0 c.lower h.ellipticity
  apply Classical.choice
  exact closureNov_original_parent_local_factory_of_map_bound c.numerical.referenceBudget
    c.geometry.source c.geometry.source_smooth c.geometry.parameter c.geometry.parameter_smooth
    c.geometry.BS c.geometry.TS c.geometry.BP c.geometry.TP c.geometry.Ds c.geometry.Dp
    c.geometry.sourcePreparation c.geometry.parameterPreparation
    (c.geometry.BS_nonneg 1) (c.geometry.BP_nonneg 1) c.geometry.Omega c.geometry.Q
    c.geometry.source_sampling c.geometry.parameter_sampling
    (fun i x hx => (c.geometry.source_bound i x hx).trans c.geometryBounds.modelRadius)
    (fun i p hp => (c.geometry.parameter_bound i p hp).trans c.geometryBounds.modelRadius)
    (c.geometryBounds.buffer.trans (min_le_left _ _))
    (c.geometryBounds.buffer.trans (min_le_right _ _))
    (c.mapBounds 3) (c.mapBounds_nonneg 3) c.numerical.mapC3 c.numerical.tensorC1
    c.lower c.numerical.first_lower c.numerical.tensor_lower
    F0 h.smooth hMap3 hEll h.phase_margin i

end AllowedMap
end ClosureNovFixedClass
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.ClosureNovFixedClass.AllowedMap.family
