import Repair.IncrementGivenPhaseTransitions

/-! The original all-observer transition differential weighted norm is
 proved finite by its actual joint jets, with a numerical prefix bound. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem increment_given_actual_transition_weighted_norm
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (j : ℕ) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) :
    paperAtlasWeighted 0 j ell (actualOriginalGivenTransitionDifferentialCoordinates Data)
      (actualOriginalGivenTransitionDomain Data) (actualOriginalGivenTransitionSample Data) ≠ ⊤ ∧
    (paperAtlasWeighted 0 j ell (actualOriginalGivenTransitionDifferentialCoordinates Data)
      (actualOriginalGivenTransitionDomain Data) (actualOriginalGivenTransitionSample Data)).toReal ≤
      (j+1)*bufferedTransitionPrefix (incrementGivenTransitionProfile (m+1) d Parameter Spatial) j := by
  let T := incrementGivenTransitionProfile (m+1) d Parameter Spatial
  have hT : ∀ k, 0 ≤ T k := incrementGivenTransitionProfile_nonneg (m+1) d Parameter Spatial hParameter hSpatial
  apply parameterRound2_paperAtlasWeighted_le_of_weighted_jets j ell (bufferedTransitionPrefix T j)
    hell hell1 (by unfold bufferedTransitionPrefix; exact add_nonneg zero_le_one (Finset.sum_nonneg (fun k _ => hT k)))
    (actualOriginalGivenTransitionDifferentialCoordinates Data)
    (actualOriginalGivenTransitionDomain Data) (actualOriginalGivenTransitionSample Data)
    (actualOriginalGivenTransitionDomain_open Data) (fun _ => inter_subset_right)
    (actualOriginalGivenTransitionDifferential_contDiffOn Data hd)
  intro ik k hk y hy
  have hBound := increment_given_actual_transition_differential_jets Data hd Parameter Spatial transition ik y hy k
  have hPrefix : T k ≤ bufferedTransitionPrefix T j := by
    have hh := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hT l)
      (show k ∈ Finset.range (j+1) by simp; omega)
    exact hh.trans (by unfold bufferedTransitionPrefix; linarith)
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell.le hell1)).trans (hBound.trans hPrefix)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_given_actual_transition_weighted_norm
