import Smoothing.Round3RepairClosedState

/-! Exact identification of the fixed packet's germs with the original
Data chart/sample germs. This is the identity on actual tensor fields.
Every original weighted seminorm agrees at every scale and derivative
order. The original samples are neither enlarged nor restricted. -/

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
local notation "Es" => EuclideanSpace ℝ (Fin n)
variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference Given : ℕ → ℝ}
variable (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
  (hK : Data.parameterSet = univ)
  (hOmega : Data.sourceNormDomain = packet.Omega) (hQ : Data.parameterNormDomain = packet.Q)
local notation "S₀" => incrementsOriginalEvaluation Data.atlas Data.parameterChart
  Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet

include hK hOmega hQ

theorem passiveOriginalPacket_germSpace_eq :
    parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ =
      parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S₀ univ := by
  rw [packet.chart_eq,← packet.originalSamples_eq_closed hK hOmega hQ]

def passiveOriginalPacketGermEquiv :
    parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ ≃ₗ[ℝ]
      parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S₀ univ where
  toFun T := ⟨T.val,(passiveOriginalPacket_germSpace_eq packet hK hOmega hQ) ▸ T.property⟩
  invFun T := ⟨T.val,(passiveOriginalPacket_germSpace_eq packet hK hOmega hQ).symm ▸ T.property⟩
  left_inv T := Subtype.ext rfl
  right_inv T := Subtype.ext rfl
  map_add' T U := Subtype.ext rfl
  map_smul' a T := Subtype.ext rfl

@[simp] theorem passiveOriginalPacketGermEquiv_val
    (T : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ) :
    (passiveOriginalPacketGermEquiv packet hK hOmega hQ T).val = T.val := rfl

@[simp] theorem passiveOriginalPacketGermEquiv_symm_val
    (T : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S₀ univ) :
    ((passiveOriginalPacketGermEquiv packet hK hOmega hQ).symm T).val = T.val := rfl

theorem passiveOriginalPacketGermEquiv_seminorm
    (hS : ∀ i, IsCompact (S₀ i)) (ell : ℝ) (j : ℕ)
    (T : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ) :
    parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S₀ univ hS
      (fun _ _ hy => hy.1) ell j (passiveOriginalPacketGermEquiv packet hK hOmega hQ T) =
    parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples
      univ packet.closedSamples_compact (fun _ _ hy => hy.1) ell j T := by
  rw [parameterRound2_originalTensorGermSeminorm_apply,parameterRound2_originalTensorGermSeminorm_apply]
  rw [passiveOriginalPacketGermEquiv_val]
  generalize T.val = U
  rw [packet.chart_eq,← packet.originalSamples_eq_closed hK hOmega hQ]

theorem passiveOriginalPacketGermEquiv_symm_seminorm
    (hS : ∀ i, IsCompact (S₀ i)) (ell : ℝ) (j : ℕ)
    (T : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S₀ univ) :
    parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples
      univ packet.closedSamples_compact (fun _ _ hy => hy.1) ell j
      ((passiveOriginalPacketGermEquiv packet hK hOmega hQ).symm T) =
    parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S₀ univ hS
      (fun _ _ hy => hy.1) ell j T := by
  have h := passiveOriginalPacketGermEquiv_seminorm packet hK hOmega hQ hS ell j
    ((passiveOriginalPacketGermEquiv packet hK hOmega hQ).symm T)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

theorem passiveOriginalPacket_tensor_weighted_eq
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart T)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S₀ =
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart T)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples := by
  rw [packet.chart_eq,← packet.originalSamples_eq_closed hK hOmega hQ]

theorem passiveOriginalPacket_map_weighted_eq
    (F : P × M → EuclideanSpace ℝ (Fin N)) (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart F)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S₀ =
    paperAtlasWeighted base j ell (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart F)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples := by
  rw [packet.chart_eq,← packet.originalSamples_eq_closed hK hOmega hQ]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginalPacketGermEquiv
#print axioms GlobalEmbedding.Continuation.passiveOriginalPacketGermEquiv_seminorm
