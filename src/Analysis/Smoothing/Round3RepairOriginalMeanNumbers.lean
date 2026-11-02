import Smoothing.Round3RepairPrimitiveProfileFactory
import Smoothing.Round3ParameterFixedCarrierCanonicalFactory

/-! The actual canonical mean factory's numerical formulas are selected
before the current SF/SH. The reserve radius, finite prefixes and every raw
input/geometry/transition cost are literal original formulas. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline
namespace GlobalEmbedding.Continuation

private local instance repairMeanNumbersFunctionalNormed (n : ℕ) :
    NormedAddCommGroup ((Fin (n*n) → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private local instance repairMeanNumbersFunctionalSpace (n : ℕ) :
    NormedSpace ℝ ((Fin (n*n) → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

def round3RepairOriginalMeanNumbers
    (m d N q Rsub Lprimary : ℕ) (c cT rho : ℝ) (hrho : 0 < rho)
    (Packet Forward Inverse Meta : ℕ → ℝ) (hPacket : ∀ j, 0 ≤ Packet j) :
    Round3RepairMeanPrimitiveProfiles :=
  let ForwardPrefix := fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k)
  let MetaPrefix := fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)
  { rho := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*Packet 0+1))
    rho_pos := div_pos hrho (by have := hPacket 0; positivity)
    reserve := rho/4
    reserve_pos := div_pos hrho (by norm_num)
    Rsub := Rsub
    Lprimary := Lprimary
    Bnd := fun s R => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+ForwardPrefix (s+(q+4))) (MetaPrefix (s+(q+4))) R Inverse
    Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+ForwardPrefix (s+(q+4))) Inverse
    Dinput := fun s => parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Inverse
    T := parameterRound2_identityRawTransition m d Packet ForwardPrefix
    Bnd_nonneg := fun s R => parameterRound2_identityRawBnd_nonneg m d N (s+(q+4))
      (Packet (s+(q+4))) c cT (1+ForwardPrefix (s+(q+4))) (MetaPrefix (s+(q+4))) R
      (hPacket _) Inverse
    Mg_nonneg := fun s => parameterRound2_identityRawMg_nonneg m d N (s+(q+4))
      (Packet (s+(q+4))) c cT (1+ForwardPrefix (s+(q+4))) Inverse
    Dinput_nonneg := fun s => parameterRound2_identityRawDinput_nonneg m d (s+(q+4))
      (Packet (s+(q+4))) (hPacket _) Inverse
    T_nonneg := parameterRound2_identityRawTransition_nonneg m d Packet ForwardPrefix hPacket
      (fun _ => round3PreparedFiniteMaximum_nonneg _) }

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3RepairOriginalMeanNumbers
