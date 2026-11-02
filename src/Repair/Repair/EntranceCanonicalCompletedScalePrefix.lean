import Probes.Round4ParameterScalePrefix
import Repair.EntranceCanonicalCompletedStagePrefix

/-!
# Exact finite-prefix closure for the scale used by the repair trajectory

The same completed mean/secondary profile and the same named numerical
cost records as the original-data endpoint determine this capped scale.
At stage k and moment q, the raw/reference profile depth is
40*(k+2)+1+(q+3)*(q+4)+4. The geometry tail constant reads only order two.
Primitive scalar geometric margins and their uniform construction remain
separate; no equality of actual maps or chosen charts is required here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uM uP uΛ uΒ uSubSecondary
variable {m d N : ℕ} {M : Type uM}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem repairEntranceCanonical_completed_stage_scale_prefix
    (radius : ℝ) (hradius : 0 < radius) (Ds Dp : ℕ)
    (BS TS BP TP Inverse Forward Given reference metricReference Meta : ℕ → ℝ)
    (BS' TS' BP' TP' Inverse' Forward' Given' reference' metricReference' Meta' : ℕ → ℝ)
    (budget normalF normalT rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q) (c cT : ℝ)
    (Mrest Cut Tinv Tobs Mrest' Cut' Tinv' Tobs' : ℕ → ℝ) (k : ℕ)
    (epsilon eta geometryTolerance linearBound reserve : ℝ)
    (hBS : ∀ j, j ≤ 40*(k+2)+1+(q+3)*(q+4)+4 → BS j = BS' j)
    (hTS : ∀ j, j ≤ 40*(k+2)+1+(q+3)*(q+4)+4 → TS j = TS' j)
    (hBP : ∀ j, j ≤ 40*(k+2)+1+(q+3)*(q+4)+4 → BP j = BP' j)
    (hTP : ∀ j, j ≤ 40*(k+2)+1+(q+3)*(q+4)+4 → TP j = TP' j)
    (hI : ∀ j, j ≤ 40*(k+2)+1+(q+3)*(q+4)+4 → Inverse j = Inverse' j)
    (hF : ∀ j, j ≤ 40*(k+2)+1+(q+3)*(q+4)+4 → Forward j = Forward' j)
    (hG : ∀ j, j ≤ 40*(k+2)+1+(q+3)*(q+4)+4 → Given j = Given' j)
    (hRef : ∀ j, j ≤ 40*(k+2)+1+(q+3)*(q+4)+4 → reference j = reference' j)
    (hMetricRef : ∀ j, j ≤ 40*(k+2)+1+(q+3)*(q+4)+4 → metricReference j = metricReference' j)
    (hMeta : ∀ j, j ≤ 40*(k+2)+1+(q+3)*(q+4)+4 → Meta j = Meta' j)
    (hRest : ∀ j, j ≤ 40*(k+2)+1 → Mrest j = Mrest' j)
    (hCut : ∀ j, j ≤ 40*(k+2)+1 → Cut j = Cut' j)
    (hInv : ∀ j, j ≤ 40*(k+2)+1+q+5 → Tinv j = Tinv' j)
    (hObs : ∀ j, j ≤ 40*(k+2)+3 → Tobs j = Tobs' j) :
    let Packet := round4ParameterStageInputProfile m d N radius hradius BS TS BP TP
      Inverse Forward Given reference Ds Dp q budget normalF normalT
    let Packet' := round4ParameterStageInputProfile m d N radius hradius BS' TS' BP' TP'
      Inverse' Forward' Given' reference' Ds Dp q budget normalF normalT
    ∀ (hPacket : ∀ k, 0 ≤ Packet k) (hPacket' : ∀ k, 0 ≤ Packet' k),
    let B0 := round4ParameterRepairReferenceProfile (m+1) d N radius hradius
      BS TS BP TP Ds Dp q metricReference budget
    let B0' := round4ParameterRepairReferenceProfile (m+1) d N radius hradius
      BS' TS' BP' TP' Ds Dp q metricReference' budget
    let p := repairEntranceCanonicalCarrierCompletedProfile.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      B0 q Rsub Lprimary Rsecondary hq rho hrho c cT Packet Forward Inverse Meta hPacket Mrest Cut Tinv Tobs
    let p' := repairEntranceCanonicalCarrierCompletedProfile.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      B0' q Rsub Lprimary Rsecondary hq rho hrho c cT Packet' Forward' Inverse' Meta' hPacket' Mrest' Cut' Tinv' Tobs'
    ∀ (cost cost' : Round3RepairPrimitiveCosts),
    RepairEntranceCanonicalCostIdentity.{uM,uP,0,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (Tr := ℝ) B0 q hq p cost →
    RepairEntranceCanonicalCostIdentity.{uM,uP,0,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (Tr := ℝ) B0' q hq p' cost' →
    min (round4ParameterNumericalBlockScale m d N
      (fun j => round4PreparedPairConstant (m+1) d radius hradius BS TS BP TP Ds Dp j q)
      cost.Cmap cost.Cmetric metricReference cost.Theta budget epsilon eta k)
      (round3RepairComputedGeometryThreshold
        (2*round4PreparedPairConstant (m+1) d radius hradius BS TS BP TP Ds Dp 0 q)
        budget (reference 0) linearBound reserve geometryTolerance/2) =
    min (round4ParameterNumericalBlockScale m d N
      (fun j => round4PreparedPairConstant (m+1) d radius hradius BS' TS' BP' TP' Ds Dp j q)
      cost'.Cmap cost'.Cmetric metricReference' cost'.Theta budget epsilon eta k)
      (round3RepairComputedGeometryThreshold
        (2*round4PreparedPairConstant (m+1) d radius hradius BS' TS' BP' TP' Ds Dp 0 q)
        budget (reference' 0) linearBound reserve geometryTolerance/2) := by
  intro Packet Packet' hPacket hPacket' B0 B0' p p' cost cost' hcost hcost'
  have hCost (j) (hj : j ≤ 40*(k+2)+1) :
      cost.Theta = cost'.Theta ∧ cost.Cmap j = cost'.Cmap j ∧ cost.Cmetric j = cost'.Cmetric j := by
    exact repairEntranceCanonical_completed_stage_costs_prefix.{uM,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N)
      radius hradius Ds Dp BS TS BP TP Inverse Forward Given reference metricReference Meta
      BS' TS' BP' TP' Inverse' Forward' Given' reference' metricReference' Meta'
      budget normalF normalT rho hrho q Rsub Lprimary Rsecondary hq c cT
      Mrest Cut Tinv Tobs Mrest' Cut' Tinv' Tobs' j
      (fun a ha => hBS a (by omega)) (fun a ha => hTS a (by omega))
      (fun a ha => hBP a (by omega)) (fun a ha => hTP a (by omega))
      (fun a ha => hI a (by omega)) (fun a ha => hF a (by omega))
      (fun a ha => hG a (by omega)) (fun a ha => hRef a (by omega))
      (fun a ha => hMetricRef a (by omega)) (fun a ha => hMeta a (by omega))
      (hRest j hj) (hCut j hj) (fun a ha => hInv a (by omega)) (fun a ha => hObs a (by omega))
      hPacket hPacket' cost cost' hcost hcost'
  have hPair (j) (hj : j ≤ 40*(k+2)+1) :
      round4PreparedPairConstant (m+1) d radius hradius BS TS BP TP Ds Dp j q =
      round4PreparedPairConstant (m+1) d radius hradius BS' TS' BP' TP' Ds Dp j q :=
    round4PreparedPairConstant_congr_prefix (m+1) d radius hradius Ds Dp j q
      (fun a ha => hBS a (by omega)) (fun a ha => hTS a (by omega))
      (fun a ha => hBP a (by omega)) (fun a ha => hTP a (by omega))
  have hTheta := (hCost 0 (Nat.zero_le _)).1
  rw [hTheta]
  rw [round4ParameterNumericalBlockScale_prefix m d N k
    (fun j => round4PreparedPairConstant (m+1) d radius hradius BS TS BP TP Ds Dp j q)
    cost.Cmap cost.Cmetric metricReference
    (fun j => round4PreparedPairConstant (m+1) d radius hradius BS' TS' BP' TP' Ds Dp j q)
    cost'.Cmap cost'.Cmetric metricReference' cost'.Theta budget epsilon eta hPair
    (fun j hj => (hCost j hj).2.1) (fun j hj => (hCost j hj).2.2)
    (fun j hj => hMetricRef j (by omega))]
  rw [hPair 0 (Nat.zero_le _),hRef 0 (Nat.zero_le _)]

#print axioms repairEntranceCanonical_completed_stage_scale_prefix
end GlobalEmbedding.Continuation
