import Probes.Round4ParameterCompletedMeanPrefix
import Probes.Round4ParameterStageInputFinite

/-!
# A finite raw prefix for the actual completed repair costs

The map, target, genuine new normal, q-step input envelope and completed
secondary budget are all expanded into the same numerical construction
used by the actual endpoint. At observation j the reference numeric prefix
is j+(q+3)*(q+4)+4. The primitive chart/template profiles and fixed scalar
margins still have to be uniformly supplied from the original setup; this
result does not replace that geometric construction by a new hypothesis.
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

theorem round4Parameter_completed_stage_costs_prefix
    (radius : ℝ) (hradius : 0 < radius) (Ds Dp : ℕ)
    (BS TS BP TP Inverse Forward Given reference metricReference Meta : ℕ → ℝ)
    (BS' TS' BP' TP' Inverse' Forward' Given' reference' metricReference' Meta' : ℕ → ℝ)
    (budget normalF normalT rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q) (c cT : ℝ)
    (Mrest Cut Tinv Tobs Mrest' Cut' Tinv' Tobs' : ℕ → ℝ) (j : ℕ)
    (hBS : ∀ k, k ≤ j+(q+3)*(q+4)+4 → BS k = BS' k)
    (hTS : ∀ k, k ≤ j+(q+3)*(q+4)+4 → TS k = TS' k)
    (hBP : ∀ k, k ≤ j+(q+3)*(q+4)+4 → BP k = BP' k)
    (hTP : ∀ k, k ≤ j+(q+3)*(q+4)+4 → TP k = TP' k)
    (hI : ∀ k, k ≤ j+(q+3)*(q+4)+4 → Inverse k = Inverse' k)
    (hF : ∀ k, k ≤ j+(q+3)*(q+4)+4 → Forward k = Forward' k)
    (hG : ∀ k, k ≤ j+(q+3)*(q+4)+4 → Given k = Given' k)
    (hRef : ∀ k, k ≤ j+(q+3)*(q+4)+4 → reference k = reference' k)
    (hMetricRef : ∀ k, k ≤ j+(q+3)*(q+4)+4 → metricReference k = metricReference' k)
    (hMeta : ∀ k, k ≤ j+(q+3)*(q+4)+4 → Meta k = Meta' k)
    (hRest : Mrest j = Mrest' j) (hCut : Cut j = Cut' j)
    (hInv : ∀ k, k ≤ j+q+5 → Tinv k = Tinv' k)
    (hObs : ∀ k, k ≤ j+2 → Tobs k = Tobs' k) :
    let Packet := round4ParameterStageInputProfile m d N radius hradius BS TS BP TP
      Inverse Forward Given reference Ds Dp q budget normalF normalT
    let Packet' := round4ParameterStageInputProfile m d N radius hradius BS' TS' BP' TP'
      Inverse' Forward' Given' reference' Ds Dp q budget normalF normalT
    ∀ (hPacket : ∀ k, 0 ≤ Packet k) (hPacket' : ∀ k, 0 ≤ Packet' k),
    let B0 := round4ParameterRepairReferenceProfile (m+1) d N radius hradius
      BS TS BP TP Ds Dp q metricReference budget
    let B0' := round4ParameterRepairReferenceProfile (m+1) d N radius hradius
      BS' TS' BP' TP' Ds Dp q metricReference' budget
    let p := round4ParameterCarrierCompletedProfile.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      B0 q Rsub Lprimary Rsecondary hq rho hrho c cT Packet Forward Inverse Meta hPacket Mrest Cut Tinv Tobs
    let p' := round4ParameterCarrierCompletedProfile.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      B0' q Rsub Lprimary Rsecondary hq rho hrho c cT Packet' Forward' Inverse' Meta' hPacket' Mrest' Cut' Tinv' Tobs'
    ∀ (cost cost' : Round3RepairPrimitiveCosts),
    Round4ParameterRepairCostIdentity.{uM,uP,0,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := ℝ) B0 q hq p cost →
    Round4ParameterRepairCostIdentity.{uM,uP,0,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := ℝ) B0' q hq p' cost' →
      cost.Theta = cost'.Theta ∧ cost.Cmap j = cost'.Cmap j ∧ cost.Cmetric j = cost'.Cmetric j := by
  intro Packet Packet' hPacket hPacket' B0 B0' p p' cost cost' hcost hcost'
  have hLow : j+(q+2)*(q+4)+2 ≤ j+(q+3)*(q+4)+4 := by
    simp only [Nat.add_mul,Nat.two_mul]
    omega
  have hB0 (k) (hk : k ≤ j+(q+2)*(q+4)) : B0 k = B0' k := by
    have hPair := round4SpatialPairConstant_congr_prefix (m+1) d N radius hradius Ds Dp k q
      (fun a ha => hBS a (by omega)) (fun a ha => hTS a (by omega))
      (fun a ha => hBP a (by omega)) (fun a ha => hTP a (by omega))
    change _*budget+(k+1)*metricReference k = _*budget+(k+1)*metricReference' k
    rw [hPair,hMetricRef k (by omega)]
  have hPacketEq (k) (hk : k ≤ j+(q+3)*(q+4)+2) : Packet k = Packet' k :=
    round4ParameterStageInputProfile_prefix_congr m d N radius hradius Ds Dp q k
      budget normalF normalT
      (fun a ha => hBS a (by omega)) (fun a ha => hTS a (by omega))
      (fun a ha => hBP a (by omega)) (fun a ha => hTP a (by omega))
      (fun a ha => hI a (by omega)) (fun a ha => hF a (by omega))
      (fun a ha => hG a (by omega)) (hRef k (by omega))
  exact round4ParameterCarrierCompletedCosts_prefix B0 B0' q Rsub Lprimary Rsecondary hq rho hrho c cT
    Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' hPacket hPacket'
    Mrest Cut Tinv Tobs Mrest' Cut' Tinv' Tobs' j hB0 hPacketEq
    (fun k hk => hF k (by omega)) (fun k hk => hI k (by omega)) (fun k hk => hMeta k (by omega))
    hRest hCut hInv hObs cost cost' hcost hcost'

#print axioms round4Parameter_completed_stage_costs_prefix
end GlobalEmbedding.Continuation
