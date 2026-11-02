import Repair.IncrementGivenPhaseTransitions

/-! Original full joint transition jets on the unchanged original samples.
This is the direct product coordinate form used by actual global plateaus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

theorem increment_actual_original_joint_transition_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (Parameter Spatial : ℕ → ℝ) (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (i k : Fin Data.atlas.count × Fin Data.parameterCount) (z : X)
    (hEval : parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i)
    (hOwner : ((Data.parameterChart i.2).prod (Data.atlas.chart i.1)).symm z ∈
      ((Data.parameterChart k.2).prod (Data.atlas.chart k.1)).source)
    (j : ℕ) (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ j (((Data.parameterChart k.2).prod (Data.atlas.chart k.1)) ∘
      ((Data.parameterChart i.2).prod (Data.atlas.chart i.1)).symm) z‖ ≤ max (Parameter j) (Spatial j) := by
  let a := parameterTensorModelEquiv (m+1) d
  have hy : a z ∈ actualOriginalGivenTransitionSample Data (i,k) := by
    refine ⟨hEval,hEval.1,?_⟩
    change incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a z) ∈
      (Data.parameterChart k.2).source ×ˢ (Data.atlas.chart k.1).source
    rw [actual_original_jointPoint_native]
    exact hOwner
  have hh := (increment_given_actual_native_transition_jets Data hd Parameter Spatial transition
    (i,k) (a z) hy j hj).2
  rw [a.symm_apply_apply] at hh
  exact hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_original_joint_transition_jets
