import Repair.EndpointFactoryNormalJets
import Repair.EndpointFactoryCutoffJets
import Repair.EndpointFactoryLinearJets
import Repair.EndpointSpatialTransitionJets
import Repair.IncrementGivenPhaseFactory

/-! A single numerical original fixed-packet budget, fixed before the
reference map, source atlas and parameter atlas. The only reference-map
values used by its j-th entry are the prescribed prefix through j+2. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ}

def repairReferenceOriginalFixedProfile
    (b : RepairReferenceFactoryBudget m d N) (cap Bs : ℝ)
    (R Parent Parameter Spatial : ℕ → ℝ) (j : ℕ) : ℝ :=
  let Joint := fun k => max (Parameter k) (Spatial k)
  (j+1)*(repairOriginalJetPrefix (repairReferenceCutoffOriginalProfile b Parent Joint) j +
    repairOriginalJetPrefix (repairReferenceNormalOriginalProfile b R Joint) j +
    repairOriginalJetPrefix (repairOriginalJointLinearProfile (m+1) d b.cover.coefficientBound
      (repairOriginalSpatialFullProfile Bs Spatial)) j +
    bufferedTransitionPrefix (incrementGivenPhaseTotalProfile (m+1) d cap b.cover.covectorBound Spatial) j +
    bufferedTransitionPrefix (incrementGivenPhaseSpatialProfile (m+1) d cap b.cover.covectorBound Spatial) j +
    bufferedTransitionPrefix (incrementGivenTransitionProfile (m+1) d Parameter Spatial) j)

theorem repairReferenceNormalOriginalProfile_prefix
    (b : RepairReferenceFactoryBudget m d N) (R U T : ℕ → ℝ) (j : ℕ)
    (h : ∀ k ≤ j+2, R k=U k) :
    repairReferenceNormalOriginalProfile b R T j=repairReferenceNormalOriginalProfile b U T j := by
  unfold repairReferenceNormalOriginalProfile repairEntranceCompositionProfile bufferedTransitionPrefix
  congr 4
  apply Finset.sum_congr rfl
  intro k hk
  unfold repairReferenceNormalNativeProfile
  rw [h (k+2) (by have := Finset.mem_range.mp hk; omega)]

theorem repairReferenceOriginalFixedProfile_prefix
    (b : RepairReferenceFactoryBudget m d N) (cap Bs : ℝ)
    (R U Parent Parameter Spatial : ℕ → ℝ) (j : ℕ)
    (h : ∀ k ≤ j+2, R k=U k) :
    repairReferenceOriginalFixedProfile b cap Bs R Parent Parameter Spatial j=
      repairReferenceOriginalFixedProfile b cap Bs U Parent Parameter Spatial j := by
  have hNormal : repairOriginalJetPrefix
      (repairReferenceNormalOriginalProfile b R (fun k => max (Parameter k) (Spatial k))) j =
      repairOriginalJetPrefix
      (repairReferenceNormalOriginalProfile b U (fun k => max (Parameter k) (Spatial k))) j := by
    apply Finset.sum_congr rfl
    intro k hk
    exact repairReferenceNormalOriginalProfile_prefix b R U _ k
      (fun l hl => h l (by have := Finset.mem_range.mp hk; omega))
  dsimp only [repairReferenceOriginalFixedProfile]
  rw [hNormal]

theorem repairReferenceOriginalFixedProfile_nonneg
    (b : RepairReferenceFactoryBudget m d N) (cap Bs : ℝ) (hCap : 0 ≤ cap) (hBs : 0 ≤ Bs)
    (R Parent Parameter Spatial : ℕ → ℝ)
    (hParent : ∀ j, 0 ≤ Parent j) (hParameter : ∀ j, 0 ≤ Parameter j)
    (hSpatial : ∀ j, 0 ≤ Spatial j) (j : ℕ) :
    0 ≤ repairReferenceOriginalFixedProfile b cap Bs R Parent Parameter Spatial j := by
  have hJoint : ∀ k, 0 ≤ max (Parameter k) (Spatial k) := fun k => (hParameter k).trans (le_max_left _ _)
  have hC := repairOriginalJetPrefix_nonneg _
    (repairReferenceCutoffOriginalProfile_nonneg b Parent _ hParent hJoint) j
  have hN := repairOriginalJetPrefix_nonneg _
    (repairReferenceNormalOriginalProfile_nonneg b R _ hJoint) j
  have hL := repairOriginalJetPrefix_nonneg _
    (repairOriginalJointLinearProfile_nonneg (m+1) d b.cover.coefficientBound b.cover.coefficientBound_pos.le
      (repairOriginalSpatialFullProfile Bs Spatial)) j
  have hP := one_le_bufferedTransitionPrefix
    (incrementGivenPhaseTotalProfile_nonneg (m+1) d cap b.cover.covectorBound Spatial hCap b.cover.covectorBound_pos.le hSpatial) j
  have hS := one_le_bufferedTransitionPrefix
    (incrementGivenPhaseSpatialProfile_nonneg (m+1) d cap b.cover.covectorBound Spatial hCap b.cover.covectorBound_pos.le hSpatial) j
  have hT := one_le_bufferedTransitionPrefix
    (incrementGivenTransitionProfile_nonneg (m+1) d Parameter Spatial hParameter hSpatial) j
  unfold repairReferenceOriginalFixedProfile
  positivity

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairReferenceOriginalFixedProfile_prefix
