import OriginalIncrements.SampledSignedNativeJets
import Repair.IncrementQuantitativeScalarRefinement
import Probes.ActualIncrementSymmetricCoordinates

/-!
# Secondary numerical costs read the original samples

The restriction reserve reads only the fixed first-jet constant. Positive
observer jets read the original Given prefix at the same sample, together
with the original transition prefix. No high derivative bound on a larger
construction neighborhood occurs in these numerical expressions.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.OriginalIncrements

def sampledSecondaryReserve (m : ℕ) (Mb kernel : ℝ) : ℝ :=
  (kernel / ((1 + 2*(1+2*Mb))^2 * actualIncrementSortedSymmetricConstant m))^2

theorem sampledSecondaryReserve_pos (m : ℕ) (Mb kernel : ℝ)
    (hMb : 0 ≤ Mb) (hKernel : 0 < kernel) :
    0 < sampledSecondaryReserve m Mb kernel := by
  exact sq_pos_of_pos (div_pos hKernel (mul_pos
    (sq_pos_of_pos (by positivity : 0 < 1 + 2*(1+2*Mb)))
    (actualIncrementSortedSymmetricConstant_pos m)))

theorem sampledSecondaryReserve_eq (m : ℕ) (Mb kernel coordinateBound : ℝ)
    (Phase : ℕ → ℝ) :
    (kernel / ((1 + incrementScalarForwardProfile Mb coordinateBound Phase 1)^2 *
      actualIncrementSortedSymmetricConstant m))^2 = sampledSecondaryReserve m Mb kernel := by
  simp only [incrementScalarForwardProfile, Nat.one_ne_zero, ite_false, ite_true,
    sampledSecondaryReserve]

theorem sampled_secondary_profiles_nonneg
    (m d : ℕ) (mu Mb : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb)
    (Packet Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j) :
    (∀ j, 0 ≤ phaseObserverForwardBudget mu Mb
      (signedPhaseFromGivenBudget m d Packet) Parameter Spatial j) ∧
    (∀ j, 0 ≤ phaseObserverInverseBudget mu Mb
      (signedPhaseFromGivenBudget m d Packet) Parameter Spatial j) := by
  constructor
  · exact incrementsCompletionPositiveObserverForwardProfile_nonneg _ _ _
      (fun j _ => phaseForwardBudget_nonneg Mb hMb _
        (fun k _ => signedPhaseFromGivenBudget_nonneg m d Packet k) j)
      (fun j _ => hParameter j) (fun j _ => hSpatial j)
  · exact incrementsCompletionPositiveObserverInverseProfile_nonneg _ _ _
      (fun j _ => phaseInverseBudget_nonneg mu Mb hmu hMb _
        (fun k _ => signedPhaseFromGivenBudget_nonneg m d Packet k) j)
      (fun j _ => hParameter j) (fun j _ => hSpatial j)

theorem sampled_secondary_profiles_prefix_congr
    (m d j : ℕ) (mu Mb : ℝ)
    (Packet Packet' Parameter Parameter' Spatial Spatial' : ℕ → ℝ)
    (hPacket : ∀ k, k ≤ j-1 → Packet k = Packet' k)
    (hParameter : ∀ k, 1 ≤ k → k ≤ j → Parameter k = Parameter' k)
    (hSpatial : ∀ k, 1 ≤ k → k ≤ j → Spatial k = Spatial' k) :
    phaseObserverForwardBudget mu Mb (signedPhaseFromGivenBudget m d Packet) Parameter Spatial j =
      phaseObserverForwardBudget mu Mb (signedPhaseFromGivenBudget m d Packet') Parameter' Spatial' j ∧
    phaseObserverInverseBudget mu Mb (signedPhaseFromGivenBudget m d Packet) Parameter Spatial j =
      phaseObserverInverseBudget mu Mb (signedPhaseFromGivenBudget m d Packet') Parameter' Spatial' j := by
  have hPhase : ∀ k, 1 ≤ k → k ≤ j →
      signedPhaseFromGivenBudget m d Packet k = signedPhaseFromGivenBudget m d Packet' k := by
    intro k hk hkj
    unfold signedPhaseFromGivenBudget
    rw [phaseFromGivenBudget_prefix_congr m d j Packet Packet' hPacket k hk hkj]
  apply incrementsCompletionPositiveObserverProfiles_prefix_congr
  · intro k hk hkj
    exact (phase_profiles_prefix_congr mu Mb _ _ k
      (fun l hl hlk => hPhase l hl (hlk.trans hkj))).1
  · intro k hk hkj
    exact (phase_profiles_prefix_congr mu Mb _ _ k
      (fun l hl hlk => hPhase l hl (hlk.trans hkj))).2
  · exact hParameter
  · exact hSpatial

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.sampledSecondaryReserve_eq
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.sampled_secondary_profiles_nonneg
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.sampled_secondary_profiles_prefix_congr
