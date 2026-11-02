import Probes.Round4ParameterCarrierMeanCosts
import Probes.Round4ParameterReservedBeforeMetric
import Smoothing.Round3RepairOriginalMeanNumbers
import Probes.Round3RepairCompletedProfiles

/-!
# The actual completed secondary budgets read a finite mean prefix

The secondary Bsec value is generated from the actual q-step mean input
profile, not supplied as a new primitive bound. Its finite dependence costs
one further (q+4) block beyond the residual profile. These are the same
`round3RepairOriginalMeanNumbers` and `complete` definitions used by the
local-primary literal raw stage in the constructed repair endpoint.
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

/-- This is definitionally the numerical mean and secondary completion in
the actual local-primary raw stage. The analytic norm costs are chosen for
arbitrary parameter manifolds, with the same local multiplicities. -/
def round4ParameterCarrierCompletedProfile
    (B0 : ℕ → ℝ) (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (rho : ℝ) (hrho : 0 < rho) (c cT : ℝ)
    (Packet Forward Inverse Meta : ℕ → ℝ) (hPacket : ∀ k, 0 ≤ Packet k)
    (Mrest Cut Tinv Tobs : ℕ → ℝ) : Round3RepairPrimitiveProfiles :=
  let mean := round3RepairOriginalMeanNumbers m d N q Rsub Lprimary c cT rho hrho
    Packet Forward Inverse Meta hPacket
  let C := round4ParameterCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
    q Rsub Lprimary hq (rho/4) (div_pos hrho (by norm_num)) c cT Packet Forward Inverse Meta hPacket
  mean.complete q (parameterRound2_uniformMeanProfile B0 C (q+4) q) Rsecondary Mrest Cut Tinv Tobs

theorem round4ParameterCarrierCompletedProfile_prefix
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
    let p := round4ParameterCarrierCompletedProfile.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      B0 q Rsub Lprimary Rsecondary hq rho hrho c cT Packet Forward Inverse Meta hPacket Mrest Cut Tinv Tobs
    let p' := round4ParameterCarrierCompletedProfile.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      B0' q Rsub Lprimary Rsecondary hq rho hrho c cT Packet' Forward' Inverse' Meta' hPacket' Mrest' Cut' Tinv' Tobs'
    p.rho = p'.rho ∧ p.Bsec j = p'.Bsec j ∧ p.Msec j = p'.Msec j ∧ p.Ccut j = p'.Ccut j ∧
    (∀ k, k ≤ j+q+5 → p.Tsec j k = p'.Tsec j k) ∧
    (∀ k, k ≤ j+q+5 → p.Tinv j k = p'.Tinv j k) ∧
    (∀ k, k ≤ j+2 → p.Tobs j k = p'.Tobs j k) := by
  intro p p'
  let reserve := rho/4
  have hreserve : 0 < reserve := div_pos hrho (by norm_num)
  let C := round4ParameterCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
    q Rsub Lprimary hq reserve hreserve c cT Packet Forward Inverse Meta hPacket
  let C' := round4ParameterCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
    q Rsub Lprimary hq reserve hreserve c cT Packet' Forward' Inverse' Meta' hPacket'
  have hBound (s) (hs : s ≤ j+(q+2)*(q+4)) : s+q+6 ≤ j+(q+3)*(q+4)+2 := by
    simp only [Nat.add_mul,Nat.two_mul,Nat.add_assoc] at *
    omega
  have hC (s) (hs : s ≤ j+(q+2)*(q+4)) (R) : C s R = C' s R :=
    round4ParameterCarrierMeanSizeCost_prefix_congr q Rsub Lprimary hq reserve hreserve c cT
      Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' hPacket hPacket' s R
      (fun k hk => hP k (hk.trans (hBound s hs)))
      (fun k hk => hF k (hk.trans (hBound s hs)))
      (fun k hk => hI k (hk.trans (hBound s hs)))
      (fun k hk => hM k (hk.trans (hBound s hs)))
  have hInput : parameterRound2_uniformMeanProfile B0 C (q+4) q (j+q+4+(q+4)) =
      parameterRound2_uniformMeanProfile B0' C' (q+4) q (j+q+4+(q+4)) := by
    apply parameterRound2_uniformMeanProfile_all_prefix_congr
    · intro k hk
      apply h0 k
      simp only [Nat.add_mul,Nat.two_mul] at *
      omega
    · intro k hk R
      apply hC k
      simp only [Nat.add_mul,Nat.two_mul] at *
      omega
  have hOrder : j+q+4+q+6 ≤ j+(q+3)*(q+4)+2 := by
    simp only [Nat.add_mul] at *
    omega
  obtain ⟨hBnd,hMg,_,hTransition⟩ := round4ParameterCarrierProfiles_prefix_congr m d N q c cT
    Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' (j+q+4)
    (fun k hk => hP k (hk.trans hOrder)) (fun k hk => hF k (hk.trans hOrder))
    (fun k hk => hI k (hk.trans hOrder)) (fun k hk => hM k (hk.trans hOrder))
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*Packet 0+1)) =
      rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*Packet' 0+1))
    rw [hP 0 (Nat.zero_le _)]
  · change max 0 (round4ParameterCarrierBnd m d N q c cT Packet Forward Inverse Meta (j+q+4)
        (parameterRound2_uniformMeanProfile B0 C (q+4) q (j+q+4+(q+4)))) =
      max 0 (round4ParameterCarrierBnd m d N q c cT Packet' Forward' Inverse' Meta' (j+q+4)
        (parameterRound2_uniformMeanProfile B0' C' (q+4) q (j+q+4+(q+4))))
    rw [hInput,hBnd]
  · change max (round4ParameterCarrierMg m d N q c cT Packet Forward Inverse (j+q+4)) (Mrest j) =
      max (round4ParameterCarrierMg m d N q c cT Packet' Forward' Inverse' (j+q+4)) (Mrest' j)
    rw [hMg,hRest]
  · change max 0 (Cut j) = max 0 (Cut' j)
    rw [hCut]
  · intro k hk
    exact hTransition k (by omega)
  · intro k hk
    change max 0 (Tinv k) = max 0 (Tinv' k)
    rw [hInv k hk]
  · intro k hk
    change max 0 (Tobs k) = max 0 (Tobs' k)
    rw [hObs k hk]

theorem round4ParameterCarrierCompletedCosts_prefix
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
  intro p p' cost cost' hcost hcost'
  obtain ⟨hr,hB,hMg,hCc,hTs,hTi,hTo⟩ := round4ParameterCarrierCompletedProfile_prefix.{uM,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M)
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
  have hmean := round4ParameterCarrierMeanCosts_prefix_congr.{uM,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) B0 B0' p.rho q Rsub Lprimary
    hq reserve hreserve c cT Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' hPacket hPacket' j
    (fun k hk => h0 k (hk.trans hLow)) (fun k hk => hP k (hk.trans hHigh))
    (fun k hk => hF k (hk.trans hHigh)) (fun k hk => hI k (hk.trans hHigh))
    (fun k hk => hM k (hk.trans hHigh))
  let Cmean := round4ParameterCarrierMeanResidualCost.{uM,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) B0 q Rsub Lprimary hq reserve hreserve c cT
    Packet Forward Inverse Meta hPacket
  let Cmean' := round4ParameterCarrierMeanResidualCost.{uM,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) B0' q Rsub Lprimary hq reserve hreserve c cT
    Packet' Forward' Inverse' Meta' hPacket'
  have hsame := round4Parameter_stage_costs_prefix_congr.{uM,0,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
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

#print axioms round4ParameterCarrierCompletedProfile_prefix
#print axioms round4ParameterCarrierCompletedCosts_prefix
end GlobalEmbedding.Continuation
