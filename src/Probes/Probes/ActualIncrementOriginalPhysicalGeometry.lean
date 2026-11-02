import Probes.ActualSecondaryPrimaryRawConsumers
import Probes.ActualIncrementRawPrimaryWave
import Probes.ActualIncrementRawPrimaryPhysical
import Probes.ActualIncrementOriginalFamilyKernel
import Probes.ActualIncrementOriginalNativeRawProducer
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Bundle Filter
open scoped ContDiff Topology BigOperators TensorProduct ENNReal Classical
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance marginSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance marginSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ}
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

variable {P : Type*} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

private local instance adaptedGeometryFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryT0Normed : NormedAddCommGroup (D →L[ℝ] Tdata) := inferInstance
private local instance adaptedGeometryT0Space : NormedSpace ℝ (D →L[ℝ] Tdata) := inferInstance
private local instance marginCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance marginCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance marginCjetNormed : NormedAddCommGroup (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCjetSpace : NormedSpace ℝ (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance marginCANormed : NormedAddCommGroup
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCASpace : NormedSpace ℝ
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance marginCBNormed : NormedAddCommGroup
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCBSpace : NormedSpace ℝ
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedSpace

private local instance rawCoeffInnerNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private local instance rawCoeffInnerSpace : NormedSpace ℝ
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance rawCoeffOuterNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance rawCoeffOuterSpace : NormedSpace ℝ
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable {Β : Type*} [Fintype Β]


private local instance globalPrimaryTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance globalPrimaryTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance globalPrimaryTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem actualOriginalPrimaryFamily_physical_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M D)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (G : Set (P × M)) (hG : IsOpen G) (cT : ℝ) (hcT : 0 < cT)
    (hTreserve : ∀ nu beta z, z ∈ (b nu beta).target → ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame
        (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
        (e nu beta z.1).symm z.2 v‖^2) :
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let g0 := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    let W := actualOriginalParameterNeighborhood Data i.2 G
    let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 G hG
    let g := parameterRound2_restrictPrimaryFamily F g0 W hW
    Nonempty (ActualOriginalPrimaryPhysicalGeometry F hF g) := by
  intro F hF g0 W hW g
  have hadapt : ∀ nu beta w, w ∈ (g.chart nu beta).source → g.phase nu w = (g.chart nu beta w).2 0 := by
    intro nu beta w hw
    exact ((hdata nu beta).2.2.2.1 w hw.1).2.symm
  have ht (nu : Fin Data.primaryCount) (beta : Β) (z : X) (hz : z ∈ (g.chart nu beta).target) :
      z ∈ (b nu beta).target := by
    rw [← (hdata nu beta).1]
    exact hz.1
  have hSlices : ∀ nu beta p, e nu beta p ∈ IsManifold.maximalAtlas 𝓙 ∞ M :=
    fun nu beta => (hdata nu beta).2.2.2.2.1
  have hSliceTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.2 ∈ (e nu beta z.1).target := by
    intro nu beta z hz
    rw [(hdata nu beta).2.2.2.2.2.2.1]
    exact ht nu beta z hz
  have hinj : ∀ nu beta z, z ∈ (g.chart nu beta).target →
      Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) (g.inverse nu beta z.1 z.2)) := by
    intro nu beta z hz
    have hs := actual_host_slice_source_point _ _ _ _ (hdata nu beta) z (ht nu beta z hz)
    have hp := (hactive nu beta _ hs).2.1
    change Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (actualOriginalOpenParameterSlice Data i z.1) _)
    rw [actualOriginalOpenParameterSlice_eq Data i z.1 hp]
    exact hImm.immersion _ hp _
  have hGram : ∀ nu beta z, z ∈ (g.chart nu beta).target →
      let pairing := incrementsTransversePairing (F z.1) (hF z.1) (g.inverse nu beta z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse nu beta z.1) z.2 a.succ)
      (pairing.comp pairing.adjoint).IsInvertible := by
    intro nu beta z hz
    exact actual_increment_transverse_gram_of_reserve (F z.1) (hF z.1)
      (e nu beta z.1).symm z.2 cT hcT (hTreserve nu beta z (ht nu beta z hz))
  have hKernel : ∀ nu beta z (hz : z ∈ (g.chart nu beta).target),
      incrementsTransversePairing (F z.1) (hF z.1) (g.inverse nu beta z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse nu beta z.1) z.2 a.succ)
        ⟨g.normal nu (z.1,g.inverse nu beta z.1 z.2),g.normal_mem nu beta z hz⟩ = 0 := by
    intro nu beta z hz
    exact actualOriginalPrimaryFamily_normal_kernel Data hd hs hn i host b e hdata eta hactive nu beta z hz.1
  exact ⟨{
    slices := e
    maximal := hSlices
    inverse := fun nu beta => rfl
    target := hSliceTarget
    immersion := hinj
    gram := hGram
    normalKernel := hKernel
    adaptation := hadapt }⟩

#print axioms actualOriginalPrimaryFamily_physical_geometry
end GlobalEmbedding.Continuation
