import Smoothing.Round3RepairCurrentState
import Smoothing.ParameterRound2IntrinsicNormalPrimaryNorm

/-! Rebind the actual current normal and shrink only its genuine primary
open domains.  Old phase, cutoff and linear costs transfer by open-domain
locality, while the new normal's actual norm is inserted explicitly.  No old
normal is declared normal to the new SF and no unchanged-profile equality is
claimed after this operation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)

def round3RepairRebindNormalData
    (Data : IncrementsOriginalNativeData n d N M P)
    (normal : Fin Data.primaryCount → P × M → Ey)
    (domain : Fin Data.primaryCount → Set (P × M)) : IncrementsOriginalNativeData n d N M P :=
  { Data with freeNormal := normal, primaryDomain := domain }

theorem round3_repair_rebind_primary_weighted_le
    (Data : IncrementsOriginalNativeData n d N M P)
    (normal : Fin Data.primaryCount → P × M → Ey)
    (domain : Fin Data.primaryCount → Set (P × M))
    (hOld : ∀ ν, IsOpen (Data.primaryDomain ν)) (hNew : ∀ ν, IsOpen (domain ν))
    (hSub : ∀ ν, domain ν ⊆ Data.primaryDomain ν)
    (ν : Fin Data.primaryCount) {a : ℕ}
    (f : (Fin Data.atlas.count × Fin Data.parameterCount) → (Fin (n+d) → ℝ) → Fin a → ℝ)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell f
      (incrementsOriginalPrimaryDifferentiation (round3RepairRebindNormalData Data normal domain) ν)
      (incrementsOriginalPrimaryEvaluation (round3RepairRebindNormalData Data normal domain) ν) ≤
    paperAtlasWeighted base j ell f
      (incrementsOriginalPrimaryDifferentiation Data ν) (incrementsOriginalPrimaryEvaluation Data ν) := by
  let E := round3RepairRebindNormalData Data normal domain
  have hEq := actual_paperAtlasWeighted_open_restrict base j ell f
    (incrementsOriginalPrimaryDifferentiation Data ν)
    (incrementsOriginalPrimaryDifferentiation E ν)
    (incrementsOriginalPrimaryEvaluation E ν)
    (actual_original_primaryDifferentiation_open Data hOld ν)
    (actual_original_primaryDifferentiation_open E hNew ν)
    (fun i y hy => ⟨hy.1,hSub ν hy.2⟩)
    (fun i y hy => ⟨hy.1.1,hy.2⟩)
  rw [← hEq]
  exact paperAtlasWeighted_mono_evaluation base j ell f _ _ _
    (fun i y hy => ⟨hy.1,hSub ν hy.2⟩)

/-- The only new numerical packet entry is the actual new normal norm.  All
other entries retain their original bounds on the genuinely smaller domains. -/
theorem round3_repair_rebind_fixed_packet_le
    (Data : IncrementsOriginalNativeData n d N M P)
    (normal : Fin Data.primaryCount → P × M → Ey)
    (domain : Fin Data.primaryCount → Set (P × M))
    (hOld : ∀ ν, IsOpen (Data.primaryDomain ν)) (hNew : ∀ ν, IsOpen (domain ν))
    (hSub : ∀ ν, domain ν ⊆ Data.primaryDomain ν)
    (j : ℕ) (ell : ℝ) (bound : ℝ≥0∞)
    (hNormal : ∀ ν, paperAtlasWeighted 0 j ell
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (normal ν))
      (incrementsOriginalPrimaryDifferentiation (round3RepairRebindNormalData Data normal domain) ν)
      (incrementsOriginalPrimaryEvaluation (round3RepairRebindNormalData Data normal domain) ν) ≤ bound) :
    parameterRound2_originalFixedPacketProfile (round3RepairRebindNormalData Data normal domain) j ell ≤
      max (parameterRound2_originalFixedPacketProfile Data j ell) bound := by
  let E := round3RepairRebindNormalData Data normal domain
  let old := parameterRound2_originalFixedPacketProfile Data j ell
  let primary := fun ν : Fin Data.primaryCount =>
    max (paperAtlasWeighted 0 j ell (incrementsOriginalScalarCoordinates Data (Data.cutoff ν))
      (incrementsOriginalPrimaryDifferentiation Data ν) (incrementsOriginalPrimaryEvaluation Data ν))
      (max (paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal ν))
        (incrementsOriginalPrimaryDifferentiation Data ν) (incrementsOriginalPrimaryEvaluation Data ν))
        (paperAtlasWeighted 0 j ell (incrementsOriginalPhaseCovectorCoordinates Data ν)
          (incrementsOriginalPrimaryDifferentiation Data ν) (incrementsOriginalPrimaryEvaluation Data ν)))
  let linear := fun ν : Fin Data.primaryCount =>
    paperAtlasWeighted 0 j ell (incrementsOriginalLinearArgumentCoordinates Data ν)
      (incrementsOriginalPrimaryDifferentiation Data ν) (incrementsOriginalPrimaryEvaluation Data ν)
  let phase := fun ν : Fin Data.primaryCount =>
    paperAtlasWeighted 0 j ell (actualOriginalTotalPhaseCoordinates Data ν)
      (incrementsOriginalPrimaryDifferentiation Data ν) (incrementsOriginalPrimaryEvaluation Data ν)
  let transition := paperAtlasWeighted 0 j ell (actualOriginalGivenTransitionDifferentialCoordinates Data)
    (actualOriginalGivenTransitionDomain Data) (actualOriginalGivenTransitionSample Data)
  have hOldEq : old = max (⨆ ν, primary ν) (max (⨆ ν, linear ν) (max (⨆ ν, phase ν) transition)) := rfl
  have hOldPrimary (ν : Fin Data.primaryCount) : primary ν ≤ old := by
    rw [hOldEq]
    exact (le_iSup primary ν).trans (le_max_left _ _)
  have hOldLinear (ν : Fin Data.primaryCount) : linear ν ≤ old := by
    rw [hOldEq]
    exact (le_iSup linear ν).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hOldPhase (ν : Fin Data.primaryCount) : phase ν ≤ old := by
    rw [hOldEq]
    exact (le_iSup phase ν).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hOldTransition : transition ≤ old := by
    rw [hOldEq]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hRestrict (ν : Fin Data.primaryCount) {a : ℕ}
      (f : (Fin Data.atlas.count × Fin Data.parameterCount) → (Fin (n+d) → ℝ) → Fin a → ℝ) :=
    round3_repair_rebind_primary_weighted_le Data normal domain hOld hNew hSub ν f 0 j ell
  change max (⨆ ν : Fin Data.primaryCount,
    max (paperAtlasWeighted 0 j ell (incrementsOriginalScalarCoordinates Data (Data.cutoff ν))
      (incrementsOriginalPrimaryDifferentiation E ν) (incrementsOriginalPrimaryEvaluation E ν))
      (max (paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (normal ν))
        (incrementsOriginalPrimaryDifferentiation E ν) (incrementsOriginalPrimaryEvaluation E ν))
        (paperAtlasWeighted 0 j ell (incrementsOriginalPhaseCovectorCoordinates Data ν)
          (incrementsOriginalPrimaryDifferentiation E ν) (incrementsOriginalPrimaryEvaluation E ν))))
    (max (⨆ ν : Fin Data.primaryCount, paperAtlasWeighted 0 j ell (incrementsOriginalLinearArgumentCoordinates Data ν)
        (incrementsOriginalPrimaryDifferentiation E ν) (incrementsOriginalPrimaryEvaluation E ν))
      (max (⨆ ν : Fin Data.primaryCount, paperAtlasWeighted 0 j ell (actualOriginalTotalPhaseCoordinates Data ν)
          (incrementsOriginalPrimaryDifferentiation E ν) (incrementsOriginalPrimaryEvaluation E ν))
        (paperAtlasWeighted 0 j ell (actualOriginalGivenTransitionDifferentialCoordinates Data)
          (actualOriginalGivenTransitionDomain Data) (actualOriginalGivenTransitionSample Data)))) ≤ max old bound
  apply max_le
  · apply iSup_le
    intro ν
    exact max_le ((hRestrict ν _).trans ((le_max_left _ _).trans ((hOldPrimary ν).trans (le_max_left _ _))))
      (max_le ((hNormal ν).trans (le_max_right _ _))
        ((hRestrict ν _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
          ((hOldPrimary ν).trans (le_max_left _ _))))))
  · exact max_le (iSup_le (fun ν => (hRestrict ν _).trans ((hOldLinear ν).trans (le_max_left _ _))))
      (max_le (iSup_le (fun ν => (hRestrict ν _).trans ((hOldPhase ν).trans (le_max_left _ _))))
        (hOldTransition.trans (le_max_left _ _)))

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem round3_repair_rebind_domain
    (Data : IncrementsOriginalNativeData n d N M P)
    (normal : Fin Data.primaryCount → P × M → Ey)
    (domain : Fin Data.primaryCount → Set (P × M))
    (hd : IncrementsOriginalDomainConditions Data)
    (hNew : ∀ ν, IsOpen (domain ν))
    (hCover : ∀ ν, incrementsOriginalRelativeCutoffSupport Data ν ⊆ domain ν) :
    IncrementsOriginalDomainConditions (round3RepairRebindNormalData Data normal domain) :=
  { hd with primary_open := hNew, cutoff_support_local := hCover }

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_rebind_primary_weighted_le
#print axioms GlobalEmbedding.Continuation.round3_repair_rebind_fixed_packet_le
