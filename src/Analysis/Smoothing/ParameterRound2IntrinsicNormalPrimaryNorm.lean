import Smoothing.ParameterRound2IntrinsicNormalCoverNorm
import Probes.ActualIncrementOriginalCoordinateJets

/-! Literal primary-domain norm binding for the actual normal cover producer.
The primary evaluation domain is unchanged. Open-domain locality identifies
the full original differentiation norm with the original PRIMARY norm, then
the finite primary supremum retains the same constant (no label count).
The estimates consumed here are exactly the outputs of the cover producer;
this file only supplies the original packet's domain and supremum identities. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem parameterRound2_original_primary_map_norm_eq_full
    (Data : IncrementsOriginalNativeData n d N M P)
    (hPrimary : ∀ ν, IsOpen (Data.primaryDomain ν))
    (ν : Fin Data.primaryCount) (f : P × M → EuclideanSpace ℝ (Fin N))
    (j : ℕ) (ell : ℝ) :
    paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart f)
      (incrementsOriginalPrimaryDifferentiation Data ν) (incrementsOriginalPrimaryEvaluation Data ν) =
    paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart f)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalPrimaryEvaluation Data ν) := by
  symm
  apply actual_paperAtlasWeighted_open_restrict
  · exact parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart
  · exact actual_original_primaryDifferentiation_open Data hPrimary ν
  · intro i y hy
    exact hy.1
  · intro i y hy
    exact ⟨hy.1.1,hy.2⟩

theorem parameterRound2_original_primary_normal_packet_bound
    (Data : IncrementsOriginalNativeData n d N M P)
    (hPrimary : ∀ ν, IsOpen (Data.primaryDomain ν))
    (normal : Fin Data.primaryCount → P × M → EuclideanSpace ℝ (Fin N))
    (j : ℕ) (ell C : ℝ) (hC : 0 ≤ C)
    (hProduced : ∀ ν,
      paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (normal ν))
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalPrimaryEvaluation Data ν) ≠ ⊤ ∧
      (paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (normal ν))
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalPrimaryEvaluation Data ν)).toReal ≤ C) :
    (⨆ ν : Fin Data.primaryCount,
      paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (normal ν))
        (incrementsOriginalPrimaryDifferentiation Data ν) (incrementsOriginalPrimaryEvaluation Data ν)) ≠ ⊤ ∧
    (⨆ ν : Fin Data.primaryCount,
      paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (normal ν))
        (incrementsOriginalPrimaryDifferentiation Data ν) (incrementsOriginalPrimaryEvaluation Data ν)).toReal ≤ C := by
  have hb (ν : Fin Data.primaryCount) :
      paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (normal ν))
        (incrementsOriginalPrimaryDifferentiation Data ν) (incrementsOriginalPrimaryEvaluation Data ν) ≤
          ENNReal.ofReal C := by
    rw [parameterRound2_original_primary_map_norm_eq_full Data hPrimary ν (normal ν) j ell]
    apply (ENNReal.toReal_le_toReal (hProduced ν).1 ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hC] using (hProduced ν).2
  have hsup := iSup_le hb
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsup,?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup).trans_eq (ENNReal.toReal_ofReal hC)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.parameterRound2_original_primary_map_norm_eq_full
#print axioms GlobalEmbedding.Continuation.parameterRound2_original_primary_normal_packet_bound
