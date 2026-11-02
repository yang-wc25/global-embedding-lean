import Probes.Round4ParameterCarrierMeanCosts
import Repair.IncrementCanonicalCostsMeanFiniteCost

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uM uP uΛ uΒ
variable {m d N : ℕ} {M : Type uM}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

def repairEntranceCanonicalCarrierMeanSizeCost
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve) (c cT : ℝ)
    (Packet Forward Inverse Meta : ℕ → ℝ) (hPacket : ∀ k, 0 ≤ Packet k) : ℕ → ℝ → ℝ :=
  incrementCanonical_round3ParameterMeanSizeCost.{uM,0,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (Tr := ℝ)
    q Rsub Lprimary hq reserve hc
    (round4ParameterCarrierBnd m d N q c cT Packet Forward Inverse Meta)
    (round4ParameterCarrierMg m d N q c cT Packet Forward Inverse)
    (round4ParameterCarrierBnd_nonneg m d N q c cT Packet Forward Inverse Meta hPacket)
    (round4ParameterCarrierMg_nonneg m d N q c cT Packet Forward Inverse)
    (round4ParameterCarrierTransition m d Packet Forward)
    (round4ParameterCarrierTransition_nonneg m d Packet Forward hPacket)

theorem repairEntranceCanonicalCarrierMeanSizeCost_prefix_congr
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve) (c cT : ℝ)
    (Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' : ℕ → ℝ)
    (hPacket : ∀ k, 0 ≤ Packet k) (hPacket' : ∀ k, 0 ≤ Packet' k) (s : ℕ) (R : ℝ)
    (hP : ∀ k, k ≤ s+q+6 → Packet k = Packet' k)
    (hF : ∀ k, k ≤ s+q+6 → Forward k = Forward' k)
    (hI : ∀ k, k ≤ s+q+6 → Inverse k = Inverse' k)
    (hM : ∀ k, k ≤ s+q+6 → Meta k = Meta' k) :
    repairEntranceCanonicalCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      q Rsub Lprimary hq reserve hc c cT Packet Forward Inverse Meta hPacket s R =
    repairEntranceCanonicalCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      q Rsub Lprimary hq reserve hc c cT Packet' Forward' Inverse' Meta' hPacket' s R := by
  obtain ⟨hB,hG,_,hTr⟩ := round4ParameterCarrierProfiles_prefix_congr m d N q c cT
    Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' s hP hF hI hM
  exact incrementCanonical_round4ParameterMeanSizeCost_prefix_congr q Rsub Lprimary hq reserve hc
    _ _ _ _ _ _ _ _ _ _ _ _ s R (hB R) hG hTr

def repairEntranceCanonicalCarrierMeanResidualCost
    (B0 : ℕ → ℝ) (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve) (c cT : ℝ)
    (Packet Forward Inverse Meta : ℕ → ℝ) (hPacket : ∀ k, 0 ≤ Packet k) : ℕ → ℝ :=
  let C := repairEntranceCanonicalCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
    q Rsub Lprimary hq reserve hc c cT Packet Forward Inverse Meta hPacket
  parameterRound2_uniformMeanResidualCost B0 C
    (fun s R => C s R*round4ParameterCarrierDinput m d q Packet Inverse s) (q+4) q

theorem repairEntranceCanonicalCarrierMeanCosts_prefix_congr
    (B0 B0' : ℕ → ℝ) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve) (c cT : ℝ)
    (Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' : ℕ → ℝ)
    (hPacket : ∀ k, 0 ≤ Packet k) (hPacket' : ∀ k, 0 ≤ Packet' k) (j : ℕ)
    (h0 : ∀ k, k ≤ j+(q+1)*(q+4) → B0 k = B0' k)
    (hP : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Packet k = Packet' k)
    (hF : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Forward k = Forward' k)
    (hI : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Inverse k = Inverse' k)
    (hM : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Meta k = Meta' k) :
    let C := repairEntranceCanonicalCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      q Rsub Lprimary hq reserve hc c cT Packet Forward Inverse Meta hPacket
    let C' := repairEntranceCanonicalCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      q Rsub Lprimary hq reserve hc c cT Packet' Forward' Inverse' Meta' hPacket'
    parameterRound2_uniformMeanThreshold B0 C rho q (q+4) =
      parameterRound2_uniformMeanThreshold B0' C' rho q (q+4) ∧
    repairEntranceCanonicalCarrierMeanResidualCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      B0 q Rsub Lprimary hq reserve hc c cT Packet Forward Inverse Meta hPacket j =
    repairEntranceCanonicalCarrierMeanResidualCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      B0' q Rsub Lprimary hq reserve hc c cT Packet' Forward' Inverse' Meta' hPacket' j := by
  intro C C'
  have hBound (s) (hs : s ≤ j+(q+1)*(q+4)) : s+q+6 ≤ j+(q+2)*(q+4)+2 := by
    simp only [Nat.add_mul,Nat.one_mul,Nat.two_mul] at *
    omega
  have hCC (s) (hs : s ≤ j+(q+1)*(q+4)) (R) : C s R = C' s R :=
    repairEntranceCanonicalCarrierMeanSizeCost_prefix_congr q Rsub Lprimary hq reserve hc c cT
      Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' hPacket hPacket' s R
      (fun k hk => hP k (hk.trans (hBound s hs)))
      (fun k hk => hF k (hk.trans (hBound s hs)))
      (fun k hk => hI k (hk.trans (hBound s hs)))
      (fun k hk => hM k (hk.trans (hBound s hs)))
  have hEntrance : q*(q+4) ≤ j+(q+1)*(q+4) := by
    simp only [Nat.add_mul,Nat.one_mul]
    omega
  constructor
  · exact parameterRound2_uniformMeanThreshold_all_prefix_congr B0 B0' C C' rho q (q+4)
      (fun k hk => h0 k (hk.trans hEntrance)) (fun k hk => hCC k (hk.trans hEntrance))
  · change parameterRound2_uniformMeanResidualCost B0 C
        (fun s R => C s R*round4ParameterCarrierDinput m d q Packet Inverse s) (q+4) q j =
      parameterRound2_uniformMeanResidualCost B0' C'
        (fun s R => C' s R*round4ParameterCarrierDinput m d q Packet' Inverse' s) (q+4) q j
    apply round4Parameter_uniformMeanResidualCost_all_prefix_congr B0 B0' C C' _ _ (q+4) q j h0 hCC
    intro s hs R
    rw [hCC s hs R]
    congr 1
    exact (round4ParameterCarrierProfiles_prefix_congr m d N q c cT
      Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' s
      (fun k hk => hP k (hk.trans (hBound s hs)))
      (fun k hk => hF k (hk.trans (hBound s hs)))
      (fun k hk => hI k (hk.trans (hBound s hs)))
      (fun k hk => hM k (hk.trans (hBound s hs)))).2.2.1

/-- When the actual inverse jets are supplied by their proved recurrence,
the same general-parameter costs read only finite forward jets; no separate
higher inverse-jet profile is needed. The first inverse reserve b and the
coordinate-value bound V remain fixed scalars. -/
theorem repairEntranceCanonicalCarrierMeanCosts_forward_prefix_congr
    (B0 B0' : ℕ → ℝ) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve) (c cT : ℝ)
    (b V : ℝ) (Packet Forward Meta Packet' Forward' Meta' : ℕ → ℝ)
    (hPacket : ∀ k, 0 ≤ Packet k) (hPacket' : ∀ k, 0 ≤ Packet' k) (j : ℕ)
    (h0 : ∀ k, k ≤ j+(q+1)*(q+4) → B0 k = B0' k)
    (hP : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Packet k = Packet' k)
    (hF : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Forward k = Forward' k)
    (hM : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Meta k = Meta' k) :
    let C := repairEntranceCanonicalCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      q Rsub Lprimary hq reserve hc c cT Packet Forward (round4InverseChartProfile b V Forward) Meta hPacket
    let C' := repairEntranceCanonicalCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      q Rsub Lprimary hq reserve hc c cT Packet' Forward' (round4InverseChartProfile b V Forward') Meta' hPacket'
    parameterRound2_uniformMeanThreshold B0 C rho q (q+4) =
      parameterRound2_uniformMeanThreshold B0' C' rho q (q+4) ∧
    repairEntranceCanonicalCarrierMeanResidualCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      B0 q Rsub Lprimary hq reserve hc c cT Packet Forward (round4InverseChartProfile b V Forward) Meta hPacket j =
    repairEntranceCanonicalCarrierMeanResidualCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N)
      B0' q Rsub Lprimary hq reserve hc c cT Packet' Forward' (round4InverseChartProfile b V Forward') Meta' hPacket' j := by
  exact repairEntranceCanonicalCarrierMeanCosts_prefix_congr B0 B0' rho q Rsub Lprimary hq reserve hc c cT
    Packet Forward (round4InverseChartProfile b V Forward) Meta
    Packet' Forward' (round4InverseChartProfile b V Forward') Meta' hPacket hPacket' j h0 hP hF
    (fun k hk => round4InverseChartProfile_congr_prefix b V k (fun i hi => hF i (hi.trans hk))) hM

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntranceCanonicalCarrierMeanSizeCost_prefix_congr
#print axioms GlobalEmbedding.Continuation.repairEntranceCanonicalCarrierMeanCosts_prefix_congr

#print axioms GlobalEmbedding.Continuation.repairEntranceCanonicalCarrierMeanCosts_forward_prefix_congr
