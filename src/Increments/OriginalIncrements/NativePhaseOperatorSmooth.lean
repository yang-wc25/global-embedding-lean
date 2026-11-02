import Probes.Round4ActualTemplateField
import Probes.ActualIncrementOriginalOpenImmersion
import GlobalEmbedding.Paper.SmoothNormedFrameNormalProjection

/-! Joint smoothness of the actual native phase operator follows from
the original map's joint smoothness and slice immersion. No quantitative
ellipticity, normal projection or second-form bound is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation.OriginalIncrements
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance nativeSmoothRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance nativeSmoothSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

private local instance nativeSmoothDVNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance nativeSmoothDVSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance nativeSmoothVVNormed : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance nativeSmoothVVSpace : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance nativeSmoothHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance nativeSmoothHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance nativeSmoothIntermediateNormed : NormedAddCommGroup ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance nativeSmoothIntermediateSpace : NormedSpace ℝ ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] V) := inferInstance

private theorem native_projected_hessian_contDiffOn
    (O : Set X) (Q : X → V →L[ℝ] V) (H : X → D →L[ℝ] D →L[ℝ] V)
    (hQ : ContDiffOn ℝ ∞ Q O) (hH : ContDiffOn ℝ ∞ H O) :
    ContDiffOn ℝ ∞ (fun z : X =>
      (ContinuousLinearMap.compL ℝ D V V (Q z)).comp (H z)) O := by
  have hC : ContDiffOn ℝ ∞
      (fun z : X => ContinuousLinearMap.compL ℝ D V V (Q z)) O :=
    (ContinuousLinearMap.compL ℝ D V V).contDiff.comp_contDiffOn
      (f := Q) hQ
  exact ContDiffOn.clm_comp (g := fun z : X => ContinuousLinearMap.compL ℝ D V V (Q z))
    (f := H) hC hH

private theorem original_native_normal_projection_contDiffOn
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    ContDiffOn ℝ ∞
      (fun z : X => (normalSpace (I := 𝓙) (actualOriginalOpenParameterSlice Data i z.1)
        ((Data.atlas.chart i.1).symm z.2)).starProjection)
      (actualOriginalNativeOpen Data i) := by
  let O := actualOriginalNativeOpen Data i
  let F := actualOriginalOpenParameterSlice Data i
  let host := Data.atlas.chart i.1
  let A := fun z : X => fderiv ℝ (F z.1 ∘ host.symm) z.2
  have hO : IsOpen O := actualOriginalNativeOpen_isOpen Data hd i
  have hJoint := actualOriginalOpenParameterSlice_native_contDiffOn Data hd hs i
  have hA : ContDiffOn ℝ ∞ A O := (incrementsJointSpatialJets_bridge
    (fun z : X => F z.1 (host.symm z.2)) O hO hJoint).2.1
  have hP := smooth_normed_frame_normal_projection A hA
    (actual_original_open_slice_first_injective Data hd hs hImm i)
  apply hP.congr
  intro z hz
  rw [actual_increment_normalSpace_eq_chart_range (F z.1)
    (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
    host (hd.atlas_smooth.chart_mem i.1) z.2
    (actualOriginalNativeMap_source_target Data i hz.1)]

theorem original_native_phase_operator_contDiffOn
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    ContDiffOn ℝ ∞
      (round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Data i)
        (fun _ => Data.atlas.chart i.1)) (actualOriginalNativeOpen Data i) := by
  let O := actualOriginalNativeOpen Data i
  let F := actualOriginalOpenParameterSlice Data i
  let host := Data.atlas.chart i.1
  let H := fun z : X => fderiv ℝ (fderiv ℝ (F z.1 ∘ host.symm)) z.2
  have hO : IsOpen O := actualOriginalNativeOpen_isOpen Data hd i
  have hJoint := actualOriginalOpenParameterSlice_native_contDiffOn Data hd hs i
  have hH : ContDiffOn ℝ ∞ H O := (incrementsJointSpatialJets_bridge
    (fun z : X => F z.1 (host.symm z.2)) O hO hJoint).2.2
  have hProjection := original_native_normal_projection_contDiffOn Data hd hs hImm i
  have hNormal : ContDiffOn ℝ ∞ (actualNormalHessianInChart F (fun _ => host)) O :=
    native_projected_hessian_contDiffOn O
      (fun z : X => (normalSpace (I := 𝓙) (F z.1) (host.symm z.2)).starProjection)
      H hProjection hH
  exact (actualHessianLift (E := D) (F := V)).contDiff.comp_contDiffOn
    (f := actualNormalHessianInChart F (fun _ => host)) hNormal

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_native_phase_operator_contDiffOn
