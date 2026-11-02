import Repair.EndpointLinearCoordinateFormula

/-! Literal Jacobian behind the original coefficient coordinates. Both chart
maps are the original source charts; all identities and smoothness statements
are restricted to their actual open overlap. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IT" => 𝓘(ℝ,D)

def repairActualObserverJacobian
    (owner observer : OpenPartialHomeomorph M D) (y : D) : D →L[ℝ] D :=
  fderiv ℝ (observer ∘ owner.symm) (owner (observer.symm y))

theorem repair_actual_observer_jacobian_at_source
    (owner observer : OpenPartialHomeomorph M D)
    (howner : owner ∈ IsManifold.maximalAtlas IT ∞ M)
    (hobserver : observer ∈ IsManifold.maximalAtlas IT ∞ M)
    (x : M) (hown : x ∈ owner.source) (hobs : x ∈ observer.source) :
    fderiv ℝ (observer ∘ owner.symm) (owner x) =
      (mfderiv IT IT observer x).comp
        (repairHostInverseDifferential owner howner x hown).toContinuousLinearMap := by
  have h := repair_reference_actual_transition_derivative owner observer howner hobserver
    (owner x) (owner.map_source hown) (by simpa only [owner.left_inv hown] using hobs)
  rw [h]
  ext v
  change mfderiv IT IT observer (owner.symm (owner x))
      (mfderiv IT IT owner.symm (owner x) v) =
    mfderiv IT IT observer x (mfderiv IT IT owner.symm (owner x) v)
  exact congrArg (fun y : M =>
    (mfderiv IT IT observer y (mfderiv IT IT owner.symm (owner x) v) : D))
    (owner.left_inv hown)

theorem repair_actual_coefficient_jacobian
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hAtlas : IsSmoothBufferedAtlas Data.atlas)
    (owner : OpenPartialHomeomorph M D)
    (howner : owner ∈ IsManifold.maximalAtlas IT ∞ M)
    (i : Fin Data.atlas.count) (x : M)
    (hown : x ∈ owner.source) (hobs : x ∈ (Data.atlas.chart i).source) :
    (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm.toContinuousLinearMap.comp
      ((incrementsOriginalSourceChartDifferential Data i x).comp
        (repairHostInverseDifferential owner howner x hown).toContinuousLinearMap) =
      fderiv ℝ (Data.atlas.chart i ∘ owner.symm) (owner x) := by
  rw [repair_actual_observer_jacobian_at_source owner (Data.atlas.chart i)
    howner (hAtlas.chart_mem i) x hown hobs]
  ext v
  rfl

theorem repair_actual_observer_jacobian_smooth
    (owner observer : OpenPartialHomeomorph M D)
    (howner : owner ∈ IsManifold.maximalAtlas IT ∞ M)
    (hobserver : observer ∈ IsManifold.maximalAtlas IT ∞ M) :
    ContDiffOn ℝ ∞ (repairActualObserverJacobian owner observer)
      (observer.symm.trans owner).source := by
  have hf := contDiffOn_actualChartTransition observer owner hobserver howner
  have hg := contDiffOn_actualChartTransition owner observer howner hobserver
  have hMap : MapsTo (owner ∘ observer.symm) (observer.symm.trans owner).source
      (owner.symm.trans observer).source := by
    intro y hy
    refine ⟨owner.map_source hy.2, ?_⟩
    change owner.symm (owner (observer.symm y)) ∈ observer.source
    have hyo : observer.symm y ∈ owner.source := hy.2
    rw [owner.left_inv hyo]
    exact observer.map_target hy.1
  exact (hg.fderiv_of_isOpen (owner.symm.trans observer).open_source
    (m := ∞) (by simp)).comp hf hMap

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_actual_coefficient_jacobian
#print axioms GlobalEmbedding.Continuation.repair_actual_observer_jacobian_smooth

