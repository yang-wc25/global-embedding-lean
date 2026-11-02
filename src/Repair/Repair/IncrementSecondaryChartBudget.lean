import Repair.IncrementSecondaryObserverProfiles
import Repair.IncrementSecondaryCutoffProfiles

/-! The numerical chart and scalar-cutoff data of the same actual secondary
packet. Inputs are the true native chart derivatives and the literal scalar
refinement, together with original atlas transitions and coordinate bounds.
No observed chart/cutoff profile or raw solver output is postulated. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
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

structure IncrementSecondaryChartBudget
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta) where
  mu : ℝ
  Mb : ℝ
  buffer : ℝ
  mu_pos : 0 < mu
  Mb_nonneg : 0 ≤ Mb
  buffer_pos : 0 < buffer
  nativeForward : ℕ → ℝ
  nativeInverse : ℕ → ℝ
  parameterTransition : ℕ → ℝ
  sourceTransition : ℕ → ℝ
  nativeForward_nonneg : ∀ j, 0 ≤ nativeForward j
  nativeInverse_nonneg : ∀ j, 0 ≤ nativeInverse j
  parameterTransition_nonneg : ∀ j, 0 ≤ parameterTransition j
  sourceTransition_nonneg : ∀ j, 0 ≤ sourceTransition j
  transition : RepairOriginalTransitionBudgets Ref parameterTransition sourceTransition
  forward : ∀ r i a j z, z ∈ (packet.piece r i a).native.source →
    ‖iteratedFDeriv ℝ j (packet.piece r i a).native z‖ ≤ nativeForward j
  inverse : ∀ r i a j z, z ∈ (packet.piece r i a).native.target →
    ‖iteratedFDeriv ℝ j (packet.piece r i a).native.symm z‖ ≤ nativeInverse j
  samples : ∀ r i a z, z ∈ (packet.piece r i a).native.source →
    parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet i
  parameterValue : ℝ
  sourceValue : ℝ
  parameterValue_nonneg : 0 ≤ parameterValue
  sourceValue_nonneg : 0 ≤ sourceValue
  parameter_value : ∀ ip z, z ∈ Ref.parameterNormDomain ip → ‖z‖ ≤ parameterValue
  source_value : ∀ ih z, z ∈ Ref.sourceNormDomain ih → ‖z‖ ≤ sourceValue
  literal : ∀ r i a, (packet.piece r i a).cutoff = actualHostRefinementCutoff
    (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1))
    (round3ParameterNativeParent (Ref.parameterChart i.2) (theta i))
    (actualRefinementCutoff X (packet.s r i) (buffer/actualPhaseRefinementFactor mu Mb) a.val)
  scalar : ∀ r i j (a : packet.s r i) x,
    buffer^j*‖iteratedFDeriv ℝ j
      (actualRefinementCutoff X (packet.s r i) (buffer/actualPhaseRefinementFactor mu Mb) a.val) x‖ ≤
        (actualPhaseRefinementFactor mu Mb)^j*actualRefinementCutoffJetCost X j

namespace IncrementSecondaryChartBudget
variable {Ref : IncrementsOriginalNativeData (m+1) d N M P}
  {hd : IncrementsOriginalDomainConditions Ref} {hs : IncrementsOriginalSmoothInputs Ref}
  {theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ}
  {packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta}
  (budget : IncrementSecondaryChartBudget Ref hd hs theta packet)

def forwardProfile : ℕ → ℝ := repairEntranceOriginalForwardProfile budget.parameterValue
  budget.nativeForward budget.parameterTransition budget.sourceTransition

def inverseProfile : ℕ → ℝ := repairEntranceOriginalInverseProfile budget.parameterValue budget.sourceValue
  budget.nativeInverse budget.parameterTransition budget.sourceTransition

def cutoffProfile (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ) : ℕ → ℝ :=
  incrementSecondaryCutoffProfile X budget.mu budget.Mb budget.buffer BS TS BP TP Ds Dp

theorem forwardProfile_nonneg (j : ℕ) : 0 ≤ budget.forwardProfile j := by
  unfold forwardProfile repairEntranceOriginalForwardProfile
  split_ifs
  · exact le_max_of_le_left budget.parameterValue_nonneg
  · exact repairEntranceCompositionProfile_nonneg _ _
      (repairEntranceCompositionProfile_nonneg _ _ budget.parameterTransition_nonneg
        (repairEntranceCompositionProfile_nonneg _ _ budget.nativeForward_nonneg budget.parameterTransition_nonneg))
      budget.sourceTransition_nonneg j

theorem inverseProfile_nonneg (j : ℕ) : 0 ≤ budget.inverseProfile j := by
  unfold inverseProfile repairEntranceOriginalInverseProfile
  split_ifs
  · exact le_max_of_le_left budget.parameterValue_nonneg
  · exact repairEntranceCompositionProfile_nonneg _ _ budget.sourceTransition_nonneg
      (repairEntranceCompositionProfile_nonneg _ _ budget.parameterTransition_nonneg
        (repairEntranceCompositionProfile_nonneg _ _ budget.nativeInverse_nonneg budget.parameterTransition_nonneg)) j

theorem cutoffProfile_nonneg (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (j : ℕ) :
    0 ≤ budget.cutoffProfile BS TS BP TP Ds Dp j :=
  incrementSecondaryCutoffProfile_nonneg X budget.mu budget.Mb budget.buffer BS TS BP TP Ds Dp j
    budget.mu_pos budget.Mb_nonneg budget.buffer_pos hBS hTS hBP hTP

end IncrementSecondaryChartBudget
end GlobalEmbedding.Continuation
