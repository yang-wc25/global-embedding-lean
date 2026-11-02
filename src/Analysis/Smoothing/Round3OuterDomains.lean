import Smoothing.ParameterLocalOriginalPairGain

/-! Receiving domains for the same actual smoothing formula. Convolution
centers still lie in the active cutoff's buffered inner chart. The receiving
chart only needs its actual target and the germ of the partition identity.
This distinction permits estimates on the original compact norm domains and
on the full sampling domains used by the next repair step. -/

noncomputable section
open Set Function
open scoped ContDiff
namespace GlobalEmbedding.Offline

variable {ι E M : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  {d : ℕ}

def round3OuterEvaluation (A : TensorBufferedChartFamily ι M E) (U : Set M)
    (i : ι) : Set E :=
  (A.chart i).target ∩ (A.chart i).symm ⁻¹' U

def round3OuterModelEvaluation (A : TensorBufferedChartFamily ι M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (U : Set M) :=
  modelCoordinateDomains c (round3OuterEvaluation A U)

theorem round3OuterModelEvaluation_subset_target
    (A : TensorBufferedChartFamily ι M E) (c : E ≃L[ℝ] (Fin d → ℝ))
    (U : Set M) (i : ι) :
    round3OuterModelEvaluation A c U i ⊆ tensorLocalModelTargets A c i :=
  fun _ hy => hy.1

theorem round3OuterModelEvaluation_univ
    (A : TensorBufferedChartFamily ι M E) (c : E ≃L[ℝ] (Fin d → ℝ)) :
    round3OuterModelEvaluation A c univ = tensorLocalModelTargets A c := by
  funext i
  ext y
  simp only [round3OuterModelEvaluation, round3OuterEvaluation, modelCoordinateDomains,
    tensorLocalModelTargets, mem_preimage, mem_inter_iff, mem_univ, and_true]

end GlobalEmbedding.Offline
