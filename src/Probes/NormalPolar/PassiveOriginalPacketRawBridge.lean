import NormalPolar.PassiveOriginalPacketGerms
import NormalPolar.ActualProbeInitialSupplyTargetCenter

/-! The actual reference and first target in the literal original Data
germ space. Their fields, every seminorm and the target-center threshold
are transported by the exact packet chart/sample identification. No new
tensor witness or estimate is chosen after a scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference Given : ℕ → ℝ}
variable (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
  (hK : Data.parameterSet = univ)
  (hOmega : Data.sourceNormDomain = packet.Omega) (hQ : Data.parameterNormDomain = packet.Q)
  (hmetric : packet.metric = Data.H)
local notation "S₀" => incrementsOriginalEvaluation Data.atlas Data.parameterChart
  Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet

def passiveOriginalPacketReferenceGerm :
    parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S₀ univ :=
  passiveOriginalPacketGermEquiv packet hK hOmega hQ (actualProbeInitialReferenceGerm packet hmetric)

def passiveOriginalPacketTargetGerm (t : ℝ) :
    parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S₀ univ :=
  passiveOriginalPacketGermEquiv packet hK hOmega hQ (actualProbeInitialTargetGerm packet hmetric t)

@[simp] theorem passiveOriginalPacketReferenceGerm_val :
    (passiveOriginalPacketReferenceGerm packet hK hOmega hQ hmetric).val = Data.H := rfl

@[simp] theorem passiveOriginalPacketTargetGerm_val (t : ℝ) :
    (passiveOriginalPacketTargetGerm packet hK hOmega hQ hmetric t).val =
      (1-((t^((6 : ℝ)/5))^10/(t^10))^2) • Data.H := rfl

theorem passiveOriginalPacket_reference_profile
    (hS : ∀ i, IsCompact (S₀ i)) (ell : ℝ) (hell1 : ell ≤ 1) (j : ℕ) :
    parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S₀ univ hS
      (fun _ _ hy => hy.1) ell j (passiveOriginalPacketReferenceGerm packet hK hOmega hQ hmetric) ≤
      actualProbeInitialReferenceProfile packet hmetric j := by
  rw [passiveOriginalPacketReferenceGerm,
    passiveOriginalPacketGermEquiv_seminorm packet hK hOmega hQ hS]
  simpa only [one_smul] using
    actualProbeInitialSupply_reference_scaled_profile packet hmetric 1 ell (by norm_num) le_rfl hell1 j

theorem passiveOriginalPacket_target_profile
    (hS : ∀ i, IsCompact (S₀ i)) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (ell : ℝ) (hell1 : ell ≤ 1) (j : ℕ) :
    parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S₀ univ hS
      (fun _ _ hy => hy.1) ell j (passiveOriginalPacketTargetGerm packet hK hOmega hQ hmetric t) ≤
      actualProbeInitialReferenceProfile packet hmetric j := by
  rw [passiveOriginalPacketTargetGerm,
    passiveOriginalPacketGermEquiv_seminorm packet hK hOmega hQ hS]
  exact (actualProbeInitialSupply_target_original_profile packet hmetric t ht ht1).2 ell hell1 j

theorem passiveOriginalPacket_target_difference (t : ℝ) (ht : 0 < t) :
    passiveOriginalPacketTargetGerm packet hK hOmega hQ hmetric t -
      passiveOriginalPacketReferenceGerm packet hK hOmega hQ hmetric =
      (-(t^4)) • passiveOriginalPacketReferenceGerm packet hK hOmega hQ hmetric := by
  apply Subtype.ext
  exact congrArg
    (fun T : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart
      packet.closedSamples univ => T.val)
    (actualProbeInitialSupply_target_difference packet hmetric t ht)

theorem passiveOriginalPacket_target_center_bound
    (hS : ∀ i, IsCompact (S₀ i)) (t : ℝ) (ht : 0 < t)
    (ell : ℝ) (hell1 : ell ≤ 1) (j : ℕ) :
    parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S₀ univ hS
      (fun _ _ hy => hy.1) ell j
      (passiveOriginalPacketTargetGerm packet hK hOmega hQ hmetric t -
        passiveOriginalPacketReferenceGerm packet hK hOmega hQ hmetric) ≤
      t^4 * actualProbeInitialReferenceProfile packet hmetric j := by
  have hEq : passiveOriginalPacketTargetGerm packet hK hOmega hQ hmetric t -
      passiveOriginalPacketReferenceGerm packet hK hOmega hQ hmetric =
      passiveOriginalPacketGermEquiv packet hK hOmega hQ
        (actualProbeInitialTargetGerm packet hmetric t - actualProbeInitialReferenceGerm packet hmetric) :=
    Subtype.ext rfl
  rw [hEq,passiveOriginalPacketGermEquiv_seminorm packet hK hOmega hQ hS]
  exact actualProbeInitialSupply_target_center_bound packet hmetric t ht ell hell1 j

theorem passiveOriginalPacket_target_center_threshold
    (hS : ∀ i, IsCompact (S₀ i)) (rho : ℝ) (hrho : 0 < rho) :
    ∃ t0 : ℝ, 0 < t0 ∧ t0 ≤ 1 ∧ ∀ t : ℝ, 0 < t → t ≤ t0 →
      ∀ ell : ℝ, ell ≤ 1 →
      parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S₀ univ hS
        (fun _ _ hy => hy.1) ell 0
        (passiveOriginalPacketTargetGerm packet hK hOmega hQ hmetric t -
          passiveOriginalPacketReferenceGerm packet hK hOmega hQ hmetric) ≤ rho/2 := by
  obtain ⟨t0,ht0,ht01,hcenter⟩ := actualProbeInitialSupply_target_center_threshold packet hmetric rho hrho
  refine ⟨t0,ht0,ht01,?_⟩
  intro t ht htt ell hell1
  have hEq : passiveOriginalPacketTargetGerm packet hK hOmega hQ hmetric t -
      passiveOriginalPacketReferenceGerm packet hK hOmega hQ hmetric =
      passiveOriginalPacketGermEquiv packet hK hOmega hQ
        (actualProbeInitialTargetGerm packet hmetric t - actualProbeInitialReferenceGerm packet hmetric) :=
    Subtype.ext rfl
  rw [hEq,passiveOriginalPacketGermEquiv_seminorm packet hK hOmega hQ hS]
  exact hcenter t ht htt ell hell1

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginalPacketReferenceGerm
#print axioms GlobalEmbedding.Continuation.passiveOriginalPacketTargetGerm
#print axioms GlobalEmbedding.Continuation.passiveOriginalPacket_target_center_threshold
