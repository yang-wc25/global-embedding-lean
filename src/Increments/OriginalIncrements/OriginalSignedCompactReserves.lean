import OriginalIncrements.AlgebraicChosenPhaseGood
import OriginalIncrements.NativePhaseOperatorSmooth
import OriginalIncrements.CompactNativeRestrictionReserve
import Probes.Round3PhaseSignedPreparation
import Probes.Round3PreparedOriginalDomains
import Probes.ActualCompactFrameOpenReserve

/-! The original signed interaction Good condition and original slice
immersion produce positive original coordinate kernel and first-derivative
reserves on one real open neighborhood of the actual compact carrier.
No adapted chart, solver, numerical conditioning or parameter-set interior
is assumed. All constants are chosen for the fixed original data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation.OriginalIncrements
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance signedCompactRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance signedCompactSquareNormed {E : Type*}
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

theorem original_signed_native_good
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (z : X) (hz : z∈actualOriginalNativeOpen Data i)
    (hpair : ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2)∈
      incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
      incrementsOriginalRelativeCutoffSupport Data r.val.1.2) :
    LinearSecondFormGoodCovector
      (round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Data i)
        (fun _=>Data.atlas.chart i.1) z).toLinearMap
      (fderiv ℝ (fun x : D => actualOriginalParameterSignedPhase Data i r.val
        (z.1,(Data.atlas.chart i.1).symm x)) z.2).toLinearMap := by
  have hGood := actual_original_parameter_signed_secondary_phase_good Data hd hs hp i r
    (z.1,(Data.atlas.chart i.1).symm z.2) hpair
  exact original_good_phase_native_operator_algebraic
    (actualOriginalOpenParameterSlice Data i)
    (actualOriginalOpenParameterSlice_contMDiff Data hd hs i)
    (Data.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1)
    (actualOriginalNativeOpen Data i) (actualOriginalNativeOpen_isOpen Data hd i)
    (actualOriginalOpenParameterSlice_native_contDiffOn Data hd hs i)
    z hz (actualOriginalNativeMap_source_target Data i hz.1)
    (fun x => actualOriginalParameterSignedPhase Data i r.val (z.1,x)) hGood

/-- Both reserves refer to the original literal native functions. The open
neighborhood contains the original compact carrier even when K has empty
parameter interior. Its points need not belong to any observation set. -/
theorem original_signed_compact_reserves
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K⊆U)
    (hUprim : U⊆actualOriginalPrimaryNativeOpen Data r.val.1.1 i ∩
      actualOriginalPrimaryNativeOpen Data r.val.1.2 i)
    (hKpair : ∀z∈K, ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2)∈
      incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
      incrementsOriginalRelativeCutoffSupport Data r.val.1.2) :
    ∃ (kernel lower : ℝ) (O : Set X),
      0<kernel ∧ 0<lower ∧ IsOpen O ∧ K⊆O ∧ O⊆U ∧
      (∀z∈O, ∀v : D, lower*‖v‖^2 ≤ ‖fderiv ℝ
        (actualOriginalParameterSlice Data i z.1 ∘ (Data.atlas.chart i.1).symm) z.2 v‖^2) ∧
      (∀z∈O, ∀v, kernel*‖v‖ ≤ ‖covectorRestriction
        (round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Data i)
          (fun _=>Data.atlas.chart i.1) z)
        (fderiv ℝ (fun x : D => actualOriginalParameterSignedPhase Data i r.val
          (z.1,(Data.atlas.chart i.1).symm x)) z.2) v‖) := by
  let F := actualOriginalOpenParameterSlice Data i
  let host := Data.atlas.chart i.1
  let B := round4ActualPhaseOperatorInChart F (fun _=>host)
  let phase := fun z : X => actualOriginalParameterSignedPhase Data i r.val (z.1,host.symm z.2)
  let xi := fun z : X => fderiv ℝ (fun x : D => phase (z.1,x)) z.2
  let A := fun z : X => fderiv ℝ (F z.1 ∘ host.symm) z.2
  have hUNative : U⊆actualOriginalNativeOpen Data i := fun z hz =>
    round3_prepared_primary_native_subset Data i r.val.1.1 (hUprim hz).1
  have hPhase : ContDiffOn ℝ ∞ phase U :=
    (round3_actual_original_signed_native_phase_smooth Data hd hs i r.val).mono hUprim
  have hxi : ContinuousOn xi U :=
    (incrementsJointSpatialJets_bridge phase U hU hPhase).2.1.continuousOn
  have hB : ContinuousOn B U :=
    ((original_native_phase_operator_contDiffOn Data hd hs hImm i).mono hUNative).continuousOn
  have hGood : ∀z∈K, LinearSecondFormGoodCovector (B z).toLinearMap (xi z).toLinearMap :=
    fun z hz => original_signed_native_good Data hd hs hp i r z (hUNative (hKU hz)) (hKpair z hz)
  obtain ⟨kernel,Ok,hKernel,hOk,hKOk,hOkU,hRestriction⟩ :=
    compact_native_restriction_reserve B xi K U hK hU hKU hB hxi hGood
  have hJoint := (actualOriginalOpenParameterSlice_native_contDiffOn Data hd hs i).mono hUNative
  have hA : ContinuousOn A U :=
    (incrementsJointSpatialJets_bridge (fun z : X => F z.1 (host.symm z.2)) U hU hJoint).2.1.continuousOn
  obtain ⟨lower,Oa,hLower,hOa,hKOa,hOaU,hFirst⟩ := actual_compact_frame_open_reserve A U K hU hK hKU hA
    (fun z hz => actual_original_open_slice_first_injective Data hd hs hImm i z (hUNative (hKU hz)))
  refine ⟨kernel,lower,Ok∩Oa,hKernel,hLower,hOk.inter hOa,
    fun z hz=>⟨hKOk hz,hKOa hz⟩,fun z hz=>hOkU hz.1,?_,?_⟩
  · intro z hz v
    have hb := hFirst z hz.2 v
    change lower*‖v‖^2 ≤ ‖fderiv ℝ
      (actualOriginalOpenParameterSlice Data i z.1 ∘ host.symm) z.2 v‖^2 at hb
    rw [actualOriginalOpenParameterSlice_eq Data i z.1
      (actualOriginalNativeOpen_parameter Data i (hUNative (hOkU hz.1)))] at hb
    exact hb
  · intro z hz v
    exact hRestriction z hz.1 v

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_signed_native_good
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_signed_compact_reserves
