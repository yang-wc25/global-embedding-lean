import Repair.IncrementActualNumericalPiece
import Repair.IncrementQuantitativeHostRefinement
import Probes.Round3PreparedOriginalDomains

/-!
# Original domains and primitive phase data for the actual signed refinement

These inputs name the genuine buffered host region. They contain original
phase derivatives and the original Sym² restriction, never an adapted
chart, stable step, solved increment, or estimate on such an output.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology TensorProduct BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance actualRegionRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance actualRegionSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

structure IncrementActualSignedRegion
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount))
    (W : Set (Ep × M)) (theta : Ep × M → ℝ)
    (mu R buffer coordinateBound kernel : ℝ) (Phase : ℕ → ℝ) where
  domain : Set X
  center : X
  isOpen : IsOpen domain
  carrier_radius : (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)) ''
    (tsupport theta ∩ actualOriginalParameterSupportPair Ref i r.val.1.1 r.val.1.2 W) ⊆ closedBall center R
  carrier_buffer : ∀ z ∈ (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)) ''
    (tsupport theta ∩ actualOriginalParameterSupportPair Ref i r.val.1.1 r.val.1.2 W), ball z buffer ⊆ domain
  target : domain ⊆ (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)).target
  parent : MapsTo (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)).symm domain W
  active : domain ⊆ actualOriginalPrimaryNativeOpen Ref r.val.1.1 i ∩ actualOriginalPrimaryNativeOpen Ref r.val.1.2 i
  inner : ∀ z ∈ domain, (Ref.atlas.chart i.1).symm z.2 ∈ Ref.atlas.inner i.1
  samples : ∀ z, z ∈ domain → parameterTensorModelEquiv (m+1) d z ∈
    incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
      Ref.parameterNormDomain Ref.parameterSet i
  coordinates : ∀ z ∈ domain, ‖z‖ ≤ coordinateBound
  phase_smooth : ContDiffOn ℝ ∞ ((actualOriginalParameterSignedPhase Ref i r.val) ∘
    (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)).symm) domain
  phase_noncritical : ∀ z ∈ (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)) ''
    (tsupport theta ∩ actualOriginalParameterSupportPair Ref i r.val.1.1 r.val.1.2 W),
    mu ≤ ‖(fderiv ℝ ((actualOriginalParameterSignedPhase Ref i r.val) ∘
      (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)).symm) z).comp
        (ContinuousLinearMap.inr ℝ Ep D)‖
  phase_jets : ∀ j z, z ∈ domain → ‖iteratedFDeriv ℝ j ((actualOriginalParameterSignedPhase Ref i r.val) ∘
    (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)).symm) z‖ ≤ Phase j
  original_kernel : ∀ y ∈ domain, ∀ v, kernel*‖v‖ ≤ ‖covectorRestriction
    (round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Ref i)
      (fun _ => Ref.atlas.chart i.1) y)
    (fderiv ℝ (fun x : D => actualOriginalParameterSignedPhase Ref i r.val
      (y.1,(Ref.atlas.chart i.1).symm x)) y.2) v‖

end GlobalEmbedding.Continuation
