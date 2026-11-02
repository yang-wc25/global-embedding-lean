import IncrementsBridge.OriginalDecompositionPartition
import IncrementsCompletion.ActivePrimaryMeanCount

/-! Original norm samples represent physical points of the original compact
parameter evaluation set. This fact imposes no condition on outside values. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem incrementsCompletion_original_evaluation_parameter
    (Data : IncrementsOriginalNativeData n d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))
    (hz : z ∈ (parameterTensorModelEquiv n d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i) :
    ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈
      Data.parameterSet ×ˢ (univ : Set M) := by
  have hp := congrArg Prod.fst ((parameterTensorModelEquiv n d).symm_apply_apply z)
  change incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z) = z.1 at hp
  have h := hz.2.2.2
  change (Data.parameterChart i.2).symm
    (incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z)) ∈ Data.parameterSet at h
  exact ⟨by rwa [hp] at h,mem_univ _⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_evaluation_parameter
