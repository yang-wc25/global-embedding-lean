import Probes.ActualIncrementOriginalNativeRawProfiles

/-! Numeric profiles for the original identity-parameter raw supplier.
Every constant is defined before the atlas, fields, input tensors or scales. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline
namespace GlobalEmbedding.Continuation

def parameterRound2_identityRawMg (m d N n : ℕ) (packet c cT Bnative : ℝ) (Tinv : ℕ → ℝ) : ℝ :=
  let Cmap := actualOriginalMapJetCost (m+1) d N n*packet
  actualAdaptedUniformGeometryCost m N n Tinv c cT Bnative Cmap Cmap

def parameterRound2_identityRawDinput (m d n : ℕ) (packet : ℝ) (Tinv : ℕ → ℝ) : ℝ :=
  let a := parameterTensorModelEquiv (m+1) d
  let Clocal := actualFastChartTransferPrefix (fun k => ‖a.toContinuousLinearMap‖*Tinv k) n *
    coordinateDimensionFactor (m+1+d) n
  let Cobs := actualFastChartTransferPrefix (fun _ => ‖a.toContinuousLinearMap‖) n *
    coordinateDimensionFactor (m+1+d) n
  2^n*‖actualOriginalCoefficientFunctional (m+1)‖*Clocal^2*packet +
    2^n*‖actualOriginalCoefficientFunctional (m+1)‖*Cobs^2*packet

def parameterRound2_identityRawBnd (m d N n : ℕ) (packet c cT Bnative Meta R : ℝ) (Tinv : ℕ → ℝ) : ℝ :=
  let Mg := parameterRound2_identityRawMg m d N n packet c cT Bnative Tinv
  let CutLocal := actualFastChartTransferPrefix Tinv n*(actualOriginalCutoffJetCost (m+1) d n*packet)
  let NormalLocal := actualFastChartTransferPrefix Tinv n*(actualOriginalNormalJetCost (m+1) d N n*packet)
  let CutObs := actualOriginalCutoffJetCost (m+1) d n*packet
  let NormalObs := actualOriginalNormalJetCost (m+1) d N n*packet
  let GradObs := actualOriginalTotalPhaseJetCost (m+1) d n*packet
  1+|Mg|+|CutLocal|+|NormalLocal|+|CutObs|+|NormalObs|+|Meta|+|GradObs|+
    parameterRound2_identityRawDinput m d n packet Tinv*max 0 R

def parameterRound2_identityRawTransition (m d : ℕ) (Packet Forward : ℕ → ℝ) (k : ℕ) : ℝ :=
  actualFastChartTransferCost (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d k*Packet k) k*Forward k

theorem parameterRound2_identityRawMg_nonneg (m d N n : ℕ) (packet c cT Bnative : ℝ) (Tinv : ℕ → ℝ) :
    0 ≤ parameterRound2_identityRawMg m d N n packet c cT Bnative Tinv :=
  actualAdaptedUniformGeometryCost_nonneg _ _ _ _ _ _ _ _ _

theorem parameterRound2_identityRawDinput_nonneg (m d n : ℕ) (packet : ℝ) (hpacket : 0 ≤ packet)
    (Tinv : ℕ → ℝ) : 0 ≤ parameterRound2_identityRawDinput m d n packet Tinv := by
  dsimp only [parameterRound2_identityRawDinput]
  positivity

theorem parameterRound2_identityRawBnd_nonneg (m d N n : ℕ) (packet c cT Bnative Meta R : ℝ)
    (hpacket : 0 ≤ packet) (Tinv : ℕ → ℝ) :
    0 ≤ parameterRound2_identityRawBnd m d N n packet c cT Bnative Meta R Tinv := by
  have hD := parameterRound2_identityRawDinput_nonneg m d n packet hpacket Tinv
  dsimp only [parameterRound2_identityRawBnd]
  positivity

theorem parameterRound2_identityRawTransition_nonneg (m d : ℕ) (Packet Forward : ℕ → ℝ)
    (hPacket : ∀ k, 0 ≤ Packet k) (hForward : ∀ k, 0 ≤ Forward k) (k : ℕ) :
    0 ≤ parameterRound2_identityRawTransition m d Packet Forward k := by
  exact mul_nonneg (actualFastChartTransferCost_nonneg _
    (fun _ => mul_nonneg (actualOriginalNativeGivenTransitionJetCost_nonneg _ _ _) (hPacket k)) k) (hForward k)

#print axioms parameterRound2_identityRawBnd_nonneg
#print axioms parameterRound2_identityRawTransition_nonneg
end GlobalEmbedding.Continuation
