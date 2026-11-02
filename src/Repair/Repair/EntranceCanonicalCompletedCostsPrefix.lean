import Repair.EntranceCanonicalCompletedProfile
import Repair.EntranceCanonicalNamedCosts

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uM uP uΛ uΒ uSubSecondary
variable {m d N : ℕ}
theorem repairEntranceCanonicalCarrierCompletedCosts_prefix
    (B0 B0' : ℕ → ℝ) (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (rho : ℝ) (hrho : 0 < rho) (c cT : ℝ)
    (Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' : ℕ → ℝ)
    (hPacket : ∀ k, 0 ≤ Packet k) (hPacket' : ∀ k, 0 ≤ Packet' k)
    (Mrest Cut Tinv Tobs Mrest' Cut' Tinv' Tobs' : ℕ → ℝ) (j : ℕ)
    (h0 : ∀ k, k ≤ j+(q+2)*(q+4) → B0 k = B0' k)
    (hP : ∀ k, k ≤ j+(q+3)*(q+4)+2 → Packet k = Packet' k)
    (hF : ∀ k, k ≤ j+(q+3)*(q+4)+2 → Forward k = Forward' k)
    (hI : ∀ k, k ≤ j+(q+3)*(q+4)+2 → Inverse k = Inverse' k)
    (hM : ∀ k, k ≤ j+(q+3)*(q+4)+2 → Meta k = Meta' k)
    (hRest : Mrest j = Mrest' j) (hCut : Cut j = Cut' j)
    (hInv : ∀ k, k ≤ j+q+5 → Tinv k = Tinv' k)
    (hObs : ∀ k, k ≤ j+2 → Tobs k = Tobs' k) :
    let p := repairEntranceCanonicalCarrierCompletedProfile.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      B0 q Rsub Lprimary Rsecondary hq rho hrho c cT Packet Forward Inverse Meta hPacket Mrest Cut Tinv Tobs
    let p' := repairEntranceCanonicalCarrierCompletedProfile.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      B0' q Rsub Lprimary Rsecondary hq rho hrho c cT Packet' Forward' Inverse' Meta' hPacket' Mrest' Cut' Tinv' Tobs'
    ∀ (cost cost' : Round3RepairPrimitiveCosts),
    RepairEntranceCanonicalCostIdentity.{uM,uP,0,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (Tr := ℝ) B0 q hq p cost →
    RepairEntranceCanonicalCostIdentity.{uM,uP,0,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (Tr := ℝ) B0' q hq p' cost' →
      cost.Theta = cost'.Theta ∧ cost.Cmap j = cost'.Cmap j ∧ cost.Cmetric j = cost'.Cmetric j := by
  intro p p' cost cost' hcost hcost'
  obtain ⟨hr,hB,hMg,hCc,hTs,hTi,hTo⟩ := repairEntranceCanonicalCarrierCompletedProfile_prefix.{uM,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N)
    B0 B0' q Rsub Lprimary Rsecondary hq rho hrho c cT
    Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' hPacket hPacket'
    Mrest Cut Tinv Tobs Mrest' Cut' Tinv' Tobs' j h0 hP hF hI hM hRest hCut hInv hObs
  let reserve := rho/4
  have hreserve : 0 < reserve := div_pos hrho (by norm_num)
  have hLow : j+(q+1)*(q+4) ≤ j+(q+2)*(q+4) := by
    simp only [Nat.add_mul,Nat.one_mul,Nat.two_mul]
    omega
  have hHigh : j+(q+2)*(q+4)+2 ≤ j+(q+3)*(q+4)+2 := by
    simp only [Nat.add_mul,Nat.two_mul]
    omega
  have hmean := repairEntranceCanonicalCarrierMeanCosts_prefix_congr.{uM,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) B0 B0' p.rho q Rsub Lprimary
    hq reserve hreserve c cT Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' hPacket hPacket' j
    (fun k hk => h0 k (hk.trans hLow)) (fun k hk => hP k (hk.trans hHigh))
    (fun k hk => hF k (hk.trans hHigh)) (fun k hk => hI k (hk.trans hHigh))
    (fun k hk => hM k (hk.trans hHigh))
  let Cmean := repairEntranceCanonicalCarrierMeanResidualCost.{uM,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) B0 q Rsub Lprimary hq reserve hreserve c cT
    Packet Forward Inverse Meta hPacket
  let Cmean' := repairEntranceCanonicalCarrierMeanResidualCost.{uM,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) B0' q Rsub Lprimary hq reserve hreserve c cT
    Packet' Forward' Inverse' Meta' hPacket'
  have hsame := repairEntranceCanonical_stage_costs_prefix_congr.{uM,0,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (Tr := ℝ)
    q Rsub Lprimary Rsecondary hq reserve hreserve p.Bsec p.Msec p.Ccut p.Tsec p.Tinv p.Tobs
    p.Bsec_nonneg p.Msec_nonneg p.Ccut_nonneg p.Tsec_nonneg p.Tinv_nonneg p.Tobs_nonneg
    p'.Bsec p'.Msec p'.Ccut p'.Tsec p'.Tinv p'.Tobs
    p'.Bsec_nonneg p'.Msec_nonneg p'.Ccut_nonneg p'.Tsec_nonneg p'.Tinv_nonneg p'.Tobs_nonneg
    Cmean Cmean' j hB hMg hCc hTs hTi hTo hmean.2
  rcases hcost with ⟨hTheta,hMap,hMetric⟩
  rcases hcost' with ⟨hTheta',hMap',hMetric'⟩
  refine ⟨?_,?_,?_⟩
  · rw [hTheta,hTheta']
    change parameterRound2_uniformMeanThreshold B0 _ p.rho q (q+4) =
      parameterRound2_uniformMeanThreshold B0' _ p'.rho q (q+4)
    rw [← hr]
    exact hmean.1
  · rw [hMap,hMap']
    exact hsame.1
  · rw [hMetric,hMetric']
    exact hsame.2

#print axioms repairEntranceCanonicalCarrierCompletedProfile_prefix
#print axioms repairEntranceCanonicalCarrierCompletedCosts_prefix
end GlobalEmbedding.Continuation
