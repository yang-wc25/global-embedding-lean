import SourceCollarsBridge.FiniteTensorGermSpace
import Repair.SourceCollarNovOriginalSamples
import Smoothing.ParameterOriginalCoreBounds
import Probes.ActualOriginalGivenProfile

/-!
# Insert the original given target in the finite internal carrier

The datum itself is unchanged. Membership is proved from original smoothness,
symmetry, and finiteness of the original given-input norms. In particular no
extra tensor, domain, auxiliary estimate or compact sampling set is supplied.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation.CollarCompletion
open SourceCollarsBridge

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- All-order finite membership is a consequence of the original input norms. -/
def originalFiniteTarget
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (ell : ℝ) (hell : 0 < ell)
    (hGiven : ∀ j, actualOriginalGivenInputProfile Data j ell ≠ ⊤) :
    finiteTensorGermSpace Data.atlas Data.parameterChart
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)
      (incrementsOriginalParameterRegion Data) (fun _ _ hy => hy.1) := by
  refine ⟨⟨Data.H,sourceCollarNov_original_target_germ_mem Data hd hs hDecomp _ subset_rfl⟩,?_⟩
  intro j
  have hCore := ne_top_of_le_ne_top (hGiven j) (actualOriginalGivenInputProfile_core_le Data j ell)
  have hWeighted := ne_top_of_le_ne_top hCore (parameterOriginalCore_tensor_le Data j ell)
  simpa only [Nat.add_zero] using parameterRound2_topOrder_finite_of_weighted 0 j hell
    (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H)
    (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) _ hWeighted

theorem originalFiniteTarget_value
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (ell : ℝ) (hell : 0 < ell)
    (hGiven : ∀ j, actualOriginalGivenInputProfile Data j ell ≠ ⊤) :
    (originalFiniteTarget Data hd hs hDecomp ell hell hGiven).val.val = Data.H := rfl

theorem originalFiniteTarget_budget
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (ell : ℝ) (hell : 0 < ell)
    (hGiven : ∀ j, actualOriginalGivenInputProfile Data j ell ≠ ⊤)
    (Packet : ℕ → ℝ) (hPacket : ∀ j, (actualOriginalGivenInputProfile Data j ell).toReal ≤ Packet j)
    (j : ℕ) :
    finiteTensorGermSeminorm Data.atlas Data.parameterChart
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)
      (incrementsOriginalParameterRegion Data) (fun _ _ hy => hy.1) ell j
      (originalFiniteTarget Data hd hs hDecomp ell hell hGiven) ≤ Packet j := by
  have hCore := ne_top_of_le_ne_top (hGiven j) (actualOriginalGivenInputProfile_core_le Data j ell)
  exact (ENNReal.toReal_mono hCore (parameterOriginalCore_tensor_le Data j ell)).trans
    ((ENNReal.toReal_mono (hGiven j) (actualOriginalGivenInputProfile_core_le Data j ell)).trans (hPacket j))

end GlobalEmbedding.Continuation.CollarCompletion
#print axioms GlobalEmbedding.Continuation.CollarCompletion.originalFiniteTarget
#print axioms GlobalEmbedding.Continuation.CollarCompletion.originalFiniteTarget_budget
