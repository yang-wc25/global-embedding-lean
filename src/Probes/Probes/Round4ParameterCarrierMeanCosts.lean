import Probes.Round4ParameterMeanFiniteCost
import Smoothing.ParameterRound2IdentityCostPrefix
import Probes.Round3PreparedFiniteAssembly
import Probes.Round4InverseFiniteProfiles

/-!
# Fixed-carrier numerical mean costs on arbitrary parameter manifolds

These are exactly the numeric profiles used by the actual after-normal
fixed-carrier mean factory. Its local primary multiplicity is a supplied
scalar. The old `identityRaw` names below refer to shared explicit numeric
formulas; the selected analytic cost is the general-parameter cost.

The order-s size cost reads Packet/Forward/Inverse/Meta through s+q+6.
The order-j finite-iteration residual and its entrance threshold therefore
read these profiles only through j+(q+2)*(q+4)+2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

def round4ParameterCarrierForwardProfile (Forward : ℕ → ℝ) (s : ℕ) : ℝ :=
  round3PreparedFiniteMaximum (fun k : Fin (s+2) => Forward k)

def round4ParameterCarrierMetaProfile (Meta : ℕ → ℝ) (s : ℕ) : ℝ :=
  round3PreparedFiniteMaximum (fun k : Fin (s+1) => Meta k)

def round4ParameterCarrierBnd (m d N q : ℕ) (c cT : ℝ)
    (Packet Forward Inverse Meta : ℕ → ℝ) (s : ℕ) (R : ℝ) : ℝ :=
  parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4))) c cT
    (1+round4ParameterCarrierForwardProfile Forward (s+(q+4)))
    (round4ParameterCarrierMetaProfile Meta (s+(q+4))) R Inverse

def round4ParameterCarrierMg (m d N q : ℕ) (c cT : ℝ)
    (Packet Forward Inverse : ℕ → ℝ) (s : ℕ) : ℝ :=
  parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4))) c cT
    (1+round4ParameterCarrierForwardProfile Forward (s+(q+4))) Inverse

def round4ParameterCarrierDinput (m d q : ℕ) (Packet Inverse : ℕ → ℝ) (s : ℕ) : ℝ :=
  parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Inverse

def round4ParameterCarrierTransition (m d : ℕ) (Packet Forward : ℕ → ℝ) : ℕ → ℝ :=
  parameterRound2_identityRawTransition m d Packet (round4ParameterCarrierForwardProfile Forward)

theorem round4ParameterCarrierBnd_nonneg (m d N q : ℕ) (c cT : ℝ)
    (Packet Forward Inverse Meta : ℕ → ℝ) (hPacket : ∀ k, 0 ≤ Packet k) (s : ℕ) (R : ℝ) :
    0 ≤ round4ParameterCarrierBnd m d N q c cT Packet Forward Inverse Meta s R :=
  parameterRound2_identityRawBnd_nonneg m d N (s+(q+4)) (Packet (s+(q+4))) c cT _ _ R
    (hPacket _) Inverse

theorem round4ParameterCarrierMg_nonneg (m d N q : ℕ) (c cT : ℝ)
    (Packet Forward Inverse : ℕ → ℝ) (s : ℕ) :
    0 ≤ round4ParameterCarrierMg m d N q c cT Packet Forward Inverse s :=
  parameterRound2_identityRawMg_nonneg m d N (s+(q+4)) (Packet (s+(q+4))) c cT _ Inverse

theorem round4ParameterCarrierDinput_nonneg (m d q : ℕ)
    (Packet Inverse : ℕ → ℝ) (hPacket : ∀ k, 0 ≤ Packet k) (s : ℕ) :
    0 ≤ round4ParameterCarrierDinput m d q Packet Inverse s :=
  parameterRound2_identityRawDinput_nonneg m d (s+(q+4)) (Packet (s+(q+4))) (hPacket _) Inverse

theorem round4ParameterCarrierTransition_nonneg (m d : ℕ)
    (Packet Forward : ℕ → ℝ) (hPacket : ∀ k, 0 ≤ Packet k) (s : ℕ) :
    0 ≤ round4ParameterCarrierTransition m d Packet Forward s :=
  parameterRound2_identityRawTransition_nonneg m d Packet (round4ParameterCarrierForwardProfile Forward)
    hPacket (fun _ => round3PreparedFiniteMaximum_nonneg _) s

theorem round4ParameterCarrierForwardProfile_prefix_congr
    (Forward Forward' : ℕ → ℝ) (s : ℕ) (h : ∀ k, k ≤ s+1 → Forward k = Forward' k) :
    round4ParameterCarrierForwardProfile Forward s = round4ParameterCarrierForwardProfile Forward' s := by
  unfold round4ParameterCarrierForwardProfile
  congr 1
  funext k
  exact h k (by have := k.isLt; omega)

theorem round4ParameterCarrierMetaProfile_prefix_congr
    (Meta Meta' : ℕ → ℝ) (s : ℕ) (h : ∀ k, k ≤ s → Meta k = Meta' k) :
    round4ParameterCarrierMetaProfile Meta s = round4ParameterCarrierMetaProfile Meta' s := by
  unfold round4ParameterCarrierMetaProfile
  congr 1
  funext k
  exact h k (by have := k.isLt; omega)

/-- Equality of the actual carrier profiles needed by the mean operator at
order s, including the observer transitions through s+1. -/
theorem round4ParameterCarrierProfiles_prefix_congr
    (m d N q : ℕ) (c cT : ℝ)
    (Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' : ℕ → ℝ) (s : ℕ)
    (hP : ∀ k, k ≤ s+q+6 → Packet k = Packet' k)
    (hF : ∀ k, k ≤ s+q+6 → Forward k = Forward' k)
    (hI : ∀ k, k ≤ s+q+6 → Inverse k = Inverse' k)
    (hM : ∀ k, k ≤ s+q+6 → Meta k = Meta' k) :
    (∀ R, round4ParameterCarrierBnd m d N q c cT Packet Forward Inverse Meta s R =
      round4ParameterCarrierBnd m d N q c cT Packet' Forward' Inverse' Meta' s R) ∧
    round4ParameterCarrierMg m d N q c cT Packet Forward Inverse s =
      round4ParameterCarrierMg m d N q c cT Packet' Forward' Inverse' s ∧
    round4ParameterCarrierDinput m d q Packet Inverse s =
      round4ParameterCarrierDinput m d q Packet' Inverse' s ∧
    (∀ k, k ≤ s+1 → round4ParameterCarrierTransition m d Packet Forward k =
      round4ParameterCarrierTransition m d Packet' Forward' k) := by
  have hFP := round4ParameterCarrierForwardProfile_prefix_congr Forward Forward' (s+(q+4))
    (fun k hk => hF k (by omega))
  have hMP := round4ParameterCarrierMetaProfile_prefix_congr Meta Meta' (s+(q+4))
    (fun k hk => hM k (by omega))
  have hPn := hP (s+(q+4)) (by omega)
  refine ⟨?_,?_,?_,?_⟩
  · intro R
    unfold round4ParameterCarrierBnd
    rw [hPn,hFP,hMP]
    exact parameterRound2_identityRawBnd_prefix_congr m d N (s+(q+4)) _ c cT _ _ R Inverse Inverse'
      (fun k hk => hI k (by omega))
  · unfold round4ParameterCarrierMg
    rw [hPn,hFP]
    exact parameterRound2_identityRawMg_prefix_congr m d N (s+(q+4)) _ c cT _ Inverse Inverse'
      (fun k hk => hI k (by omega))
  · unfold round4ParameterCarrierDinput
    rw [hPn]
    exact parameterRound2_identityRawDinput_prefix_congr m d (s+(q+4)) _ Inverse Inverse'
      (fun k hk => hI k (by omega))
  · apply parameterRound2_identityRawTransition_prefix_congr m d (s+1)
    · intro k hk
      exact hP k (by omega)
    · intro k hk
      exact round4ParameterCarrierForwardProfile_prefix_congr Forward Forward' k
        (fun a ha => hF a (by omega))

universe uM uP uΛ uΒ
variable {m d N : ℕ} {M : Type uM}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

def round4ParameterCarrierMeanSizeCost
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve) (c cT : ℝ)
    (Packet Forward Inverse Meta : ℕ → ℝ) (hPacket : ∀ k, 0 ≤ Packet k) : ℕ → ℝ → ℝ :=
  round3ParameterMeanSizeCost.{uM,0,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
    q Rsub Lprimary hq reserve hc
    (round4ParameterCarrierBnd m d N q c cT Packet Forward Inverse Meta)
    (round4ParameterCarrierMg m d N q c cT Packet Forward Inverse)
    (round4ParameterCarrierBnd_nonneg m d N q c cT Packet Forward Inverse Meta hPacket)
    (round4ParameterCarrierMg_nonneg m d N q c cT Packet Forward Inverse)
    (round4ParameterCarrierTransition m d Packet Forward)
    (round4ParameterCarrierTransition_nonneg m d Packet Forward hPacket)

theorem round4ParameterCarrierMeanSizeCost_prefix_congr
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve) (c cT : ℝ)
    (Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' : ℕ → ℝ)
    (hPacket : ∀ k, 0 ≤ Packet k) (hPacket' : ∀ k, 0 ≤ Packet' k) (s : ℕ) (R : ℝ)
    (hP : ∀ k, k ≤ s+q+6 → Packet k = Packet' k)
    (hF : ∀ k, k ≤ s+q+6 → Forward k = Forward' k)
    (hI : ∀ k, k ≤ s+q+6 → Inverse k = Inverse' k)
    (hM : ∀ k, k ≤ s+q+6 → Meta k = Meta' k) :
    round4ParameterCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lprimary hq reserve hc c cT Packet Forward Inverse Meta hPacket s R =
    round4ParameterCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lprimary hq reserve hc c cT Packet' Forward' Inverse' Meta' hPacket' s R := by
  obtain ⟨hB,hG,_,hTr⟩ := round4ParameterCarrierProfiles_prefix_congr m d N q c cT
    Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' s hP hF hI hM
  exact round4ParameterMeanSizeCost_prefix_congr q Rsub Lprimary hq reserve hc
    _ _ _ _ _ _ _ _ _ _ _ _ s R (hB R) hG hTr

def round4ParameterCarrierMeanResidualCost
    (B0 : ℕ → ℝ) (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve) (c cT : ℝ)
    (Packet Forward Inverse Meta : ℕ → ℝ) (hPacket : ∀ k, 0 ≤ Packet k) : ℕ → ℝ :=
  let C := round4ParameterCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
    q Rsub Lprimary hq reserve hc c cT Packet Forward Inverse Meta hPacket
  parameterRound2_uniformMeanResidualCost B0 C
    (fun s R => C s R*round4ParameterCarrierDinput m d q Packet Inverse s) (q+4) q

theorem round4ParameterCarrierMeanCosts_prefix_congr
    (B0 B0' : ℕ → ℝ) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve) (c cT : ℝ)
    (Packet Forward Inverse Meta Packet' Forward' Inverse' Meta' : ℕ → ℝ)
    (hPacket : ∀ k, 0 ≤ Packet k) (hPacket' : ∀ k, 0 ≤ Packet' k) (j : ℕ)
    (h0 : ∀ k, k ≤ j+(q+1)*(q+4) → B0 k = B0' k)
    (hP : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Packet k = Packet' k)
    (hF : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Forward k = Forward' k)
    (hI : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Inverse k = Inverse' k)
    (hM : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Meta k = Meta' k) :
    let C := round4ParameterCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lprimary hq reserve hc c cT Packet Forward Inverse Meta hPacket
    let C' := round4ParameterCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lprimary hq reserve hc c cT Packet' Forward' Inverse' Meta' hPacket'
    parameterRound2_uniformMeanThreshold B0 C rho q (q+4) =
      parameterRound2_uniformMeanThreshold B0' C' rho q (q+4) ∧
    round4ParameterCarrierMeanResidualCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      B0 q Rsub Lprimary hq reserve hc c cT Packet Forward Inverse Meta hPacket j =
    round4ParameterCarrierMeanResidualCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      B0' q Rsub Lprimary hq reserve hc c cT Packet' Forward' Inverse' Meta' hPacket' j := by
  intro C C'
  have hBound (s) (hs : s ≤ j+(q+1)*(q+4)) : s+q+6 ≤ j+(q+2)*(q+4)+2 := by
    simp only [Nat.add_mul,Nat.one_mul,Nat.two_mul] at *
    omega
  have hCC (s) (hs : s ≤ j+(q+1)*(q+4)) (R) : C s R = C' s R :=
    round4ParameterCarrierMeanSizeCost_prefix_congr q Rsub Lprimary hq reserve hc c cT
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
theorem round4ParameterCarrierMeanCosts_forward_prefix_congr
    (B0 B0' : ℕ → ℝ) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve) (c cT : ℝ)
    (b V : ℝ) (Packet Forward Meta Packet' Forward' Meta' : ℕ → ℝ)
    (hPacket : ∀ k, 0 ≤ Packet k) (hPacket' : ∀ k, 0 ≤ Packet' k) (j : ℕ)
    (h0 : ∀ k, k ≤ j+(q+1)*(q+4) → B0 k = B0' k)
    (hP : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Packet k = Packet' k)
    (hF : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Forward k = Forward' k)
    (hM : ∀ k, k ≤ j+(q+2)*(q+4)+2 → Meta k = Meta' k) :
    let C := round4ParameterCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lprimary hq reserve hc c cT Packet Forward (round4InverseChartProfile b V Forward) Meta hPacket
    let C' := round4ParameterCarrierMeanSizeCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lprimary hq reserve hc c cT Packet' Forward' (round4InverseChartProfile b V Forward') Meta' hPacket'
    parameterRound2_uniformMeanThreshold B0 C rho q (q+4) =
      parameterRound2_uniformMeanThreshold B0' C' rho q (q+4) ∧
    round4ParameterCarrierMeanResidualCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      B0 q Rsub Lprimary hq reserve hc c cT Packet Forward (round4InverseChartProfile b V Forward) Meta hPacket j =
    round4ParameterCarrierMeanResidualCost.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M)
      B0' q Rsub Lprimary hq reserve hc c cT Packet' Forward' (round4InverseChartProfile b V Forward') Meta' hPacket' j := by
  exact round4ParameterCarrierMeanCosts_prefix_congr B0 B0' rho q Rsub Lprimary hq reserve hc c cT
    Packet Forward (round4InverseChartProfile b V Forward) Meta
    Packet' Forward' (round4InverseChartProfile b V Forward') Meta' hPacket hPacket' j h0 hP hF
    (fun k hk => round4InverseChartProfile_congr_prefix b V k (fun i hi => hF i (hi.trans hk))) hM

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterCarrierProfiles_prefix_congr
#print axioms GlobalEmbedding.Continuation.round4ParameterCarrierMeanSizeCost_prefix_congr
#print axioms GlobalEmbedding.Continuation.round4ParameterCarrierMeanCosts_prefix_congr

#print axioms GlobalEmbedding.Continuation.round4ParameterCarrierMeanCosts_forward_prefix_congr
