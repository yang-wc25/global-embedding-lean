import Probes.Round4ParameterEntryBeforeMetric
import Probes.Round4ParameterCompletedStagePrefix

/-!
# The actual repair block scale is a finite numerical expression

The displayed formula evaluates the recurrence constants only at the
current and next controlled orders and the displacement cost at k/2.
It is identified with the exact block scale used by the actual trajectory.
Thus no high-order tail of a selected constant profile can silently enter
this scale. Uniform generation of primitive geometric margins remains a
separate requirement.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

def round4ParameterNumericalBlockScale (m d N : ℕ)
    (Cs Cmap Cmetric reference : ℕ → ℝ) (Theta budget epsilon eta : ℝ) (k : ℕ) : ℝ :=
  let Cpair := round3RepairClosedPairCost (m := m) (d := d) (N := N) Cs Cmap Cmetric
  let Cd := round3RepairClosedTensorCost (m := m) (d := d) (N := N) Cs Cmap Cmetric
  let rate := fun j : ℕ => 1+j*reference j+2*Cpair j*(1+budget)
  min (min ((1/2 : ℝ)^5) (min (epsilon/(8*(Cmap (k/2)+1)))
    (min ((budget/(4*(max (rate (40*(k+1))) (rate (40*(k+2)))*(1+budget)+1)))^5)
      ((eta/(2*Cd 0*(1+budget)^2+1))^5)))) (Theta^10/2)

theorem round4ParameterNumericalBlockScale_prefix
    (m d N k : ℕ) (Cs Cmap Cmetric reference Cs' Cmap' Cmetric' reference' : ℕ → ℝ)
    (Theta budget epsilon eta : ℝ)
    (hS : ∀ j, j ≤ 40*(k+2)+1 → Cs j = Cs' j)
    (hU : ∀ j, j ≤ 40*(k+2)+1 → Cmap j = Cmap' j)
    (hR : ∀ j, j ≤ 40*(k+2)+1 → Cmetric j = Cmetric' j)
    (hRef : ∀ j, j ≤ 40*(k+2)+1 → reference j = reference' j) :
    round4ParameterNumericalBlockScale m d N Cs Cmap Cmetric reference Theta budget epsilon eta k =
      round4ParameterNumericalBlockScale m d N Cs' Cmap' Cmetric' reference' Theta budget epsilon eta k := by
  have h0 : 0 ≤ 40*(k+2)+1 := Nat.zero_le _
  have hk : k/2 ≤ 40*(k+2)+1 := by omega
  have hcur : 40*(k+1) ≤ 40*(k+2)+1 := by omega
  have hcur1 : 40*(k+1)+1 ≤ 40*(k+2)+1 := by omega
  have hnxt : 40*(k+2) ≤ 40*(k+2)+1 := by omega
  simp only [round4ParameterNumericalBlockScale,round3RepairClosedPairCost,round3RepairClosedTensorCost,
    hS 0 h0,hS (40*(k+1)) hcur,hS (40*(k+2)) hnxt,
    hU 0 h0,hU (k/2) hk,hU (40*(k+1)) hcur,hU (40*(k+2)) hnxt,
    hU (40*(k+1)+1) hcur1,hU (40*(k+2)+1) le_rfl,
    hR 0 h0,hR (40*(k+1)) hcur,hR (40*(k+2)) hnxt,
    hRef (40*(k+1)) hcur,hRef (40*(k+2)) hnxt]

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

theorem round4ParameterBlockScale_eq_numerical
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (Cs : ℕ → ℝ) (cost : Round3RepairPrimitiveCosts) (budget epsilon eta : ℝ) (k : ℕ) :
    round4ParameterBlockScale packet Cs cost budget epsilon eta k =
      round4ParameterNumericalBlockScale m d N Cs cost.Cmap cost.Cmetric packet.closedReferenceProfile
        cost.Theta budget epsilon eta k := by
  have hRate (Cpair : ℕ → ℝ) (j : ℕ) : round3RepairClosedStateRate packet Cpair budget j =
      1+j*packet.closedReferenceProfile j+2*Cpair j*(1+budget) := by
    unfold round3RepairClosedStateRate Round3RepairFixedSmoothingPacket.closedReferenceProfile
    rw [packet.reference_tensor]
  unfold round4ParameterBlockScale round3RepairClosedNumericalThreshold round4ParameterNumericalBlockScale
  rw [hRate,hRate]

/-- Applied directly to the numerical cost records in the actual endpoint.
The reference sampling data and scalar geometric cap remain fixed. -/
theorem round4Parameter_actual_block_scale_prefix
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (Cs Cs' : ℕ → ℝ) (cost cost' : Round3RepairPrimitiveCosts) (budget epsilon eta cap : ℝ) (k : ℕ)
    (hS : ∀ j, j ≤ 40*(k+2)+1 → Cs j = Cs' j)
    (hTheta : cost.Theta = cost'.Theta)
    (hU : ∀ j, j ≤ 40*(k+2)+1 → cost.Cmap j = cost'.Cmap j)
    (hR : ∀ j, j ≤ 40*(k+2)+1 → cost.Cmetric j = cost'.Cmetric j) :
    min (round4ParameterBlockScale packet Cs cost budget epsilon eta k) (cap/2) =
      min (round4ParameterBlockScale packet Cs' cost' budget epsilon eta k) (cap/2) := by
  rw [round4ParameterBlockScale_eq_numerical,round4ParameterBlockScale_eq_numerical,hTheta]
  rw [round4ParameterNumericalBlockScale_prefix m d N k Cs cost.Cmap cost.Cmetric packet.closedReferenceProfile
    Cs' cost'.Cmap cost'.Cmetric packet.closedReferenceProfile cost'.Theta budget epsilon eta
    hS hU hR (fun _ _ => rfl)]

#print axioms round4ParameterNumericalBlockScale_prefix
#print axioms round4ParameterBlockScale_eq_numerical
#print axioms round4Parameter_actual_block_scale_prefix
end GlobalEmbedding.Continuation
