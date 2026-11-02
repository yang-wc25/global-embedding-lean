import Repair.FullIncrementNovOpenMeanNorms
import Smoothing.ParameterRound2IdentityCostPrefix
import Smoothing.ParameterRound2UniformMeanAnalyticPrefix
import CollarCompletion.FiniteOpenMeanIteration

/-!
# Numerical profiles for the actual finite original mean

These are the exact costs used by the original raw constructor and physical
mean estimate. Their definitions do not contain an input datum, parameter
space, parameter atlas, original tensor, scale, or later observation order
in the entrance threshold. The proved prefix equality includes changes of
all four profiles, including the raw native budgets and transition costs.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation.CollarCompletion
universe uM uB
variable {m d N : ℕ} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

/-- The actual native mean size constant, with finite transition reads. -/
def finiteOriginalMeanSizeCost
    (q Rsub Lprimary : ℕ) (rho c cT : ℝ) (hrho : 0 < rho)
    (Packet Forward Meta Tinv : ℕ → ℝ)
    (hPacket : ∀ k, 0 ≤ Packet k) (hForward : ∀ k, 0 ≤ Forward k) : ℕ → ℝ → ℝ :=
  fun s R => fullIncrementNovMeanNormCost.{uM,uB}
    (m := m) (d := d) (N := N) (M := M) (s+(q+4)) q s Rsub Lprimary (by omega)
    (rho/4)
    (parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) R Tinv)
    (parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) Tinv)
    (div_pos hrho (by norm_num))
    (parameterRound2_identityRawBnd_nonneg _ _ _ _ _ _ _ _ _ _ (hPacket _) _)
    (parameterRound2_identityRawMg_nonneg _ _ _ _ _ _ _ _ _)
    (parameterRound2_identityRawTransition m d Packet Forward)
    (parameterRound2_identityRawTransition_nonneg m d Packet Forward hPacket hForward)

/-- Difference cost uses the same native profile and original input distance. -/
def finiteOriginalMeanDifferenceCost
    (q Rsub Lprimary : ℕ) (rho c cT : ℝ) (hrho : 0 < rho)
    (Packet Forward Meta Tinv : ℕ → ℝ)
    (hPacket : ∀ k, 0 ≤ Packet k) (hForward : ∀ k, 0 ≤ Forward k) : ℕ → ℝ → ℝ :=
  fun s R => finiteOriginalMeanSizeCost.{uM,uB} (m := m) (d := d) (N := N) (M := M)
    q Rsub Lprimary rho c cT hrho Packet Forward Meta Tinv hPacket hForward s R *
    parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Tinv

/-- Exact threshold for the same physical mean iteration. -/
def finiteOriginalMeanThreshold
    (q Rsub Lprimary : ℕ) (rho c cT : ℝ) (hrho : 0 < rho)
    (Packet Forward Meta Tinv : ℕ → ℝ)
    (hPacket : ∀ k, 0 ≤ Packet k) (hForward : ∀ k, 0 ≤ Forward k) : ℝ :=
  parameterRound2_uniformMeanThreshold Packet
    (finiteOriginalMeanSizeCost.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lprimary rho c cT hrho Packet Forward Meta Tinv hPacket hForward)
    (rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*Packet 0+1))) q (q+4)

theorem finiteOriginalMeanSizeCost_prefix_congr
    (q Rsub Lprimary : ℕ) (rho c cT : ℝ) (hrho : 0 < rho)
    (Packet Forward Meta Tinv Packet' Forward' Meta' Tinv' : ℕ → ℝ)
    (hPacket : ∀ k, 0 ≤ Packet k) (hForward : ∀ k, 0 ≤ Forward k)
    (hPacket' : ∀ k, 0 ≤ Packet' k) (hForward' : ∀ k, 0 ≤ Forward' k)
    (s : ℕ)
    (hP : ∀ k, k ≤ s+(q+4) → Packet k = Packet' k)
    (hF : ∀ k, k ≤ s+(q+4) → Forward k = Forward' k)
    (hMeta : Meta (s+(q+4)) = Meta' (s+(q+4)))
    (hInv : ∀ k, k ≤ s+(q+4)+2 → Tinv k = Tinv' k) (R : ℝ) :
    finiteOriginalMeanSizeCost.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lprimary rho c cT hrho Packet Forward Meta Tinv hPacket hForward s R =
    finiteOriginalMeanSizeCost.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lprimary rho c cT hrho Packet' Forward' Meta' Tinv' hPacket' hForward' s R := by
  have hBnd := parameterRound2_identityRawBnd_prefix_congr m d N (s+(q+4))
    (Packet (s+(q+4))) c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) R Tinv Tinv' hInv
  rw [hP _ le_rfl,hF _ le_rfl,hMeta] at hBnd
  have hMg := parameterRound2_identityRawMg_prefix_congr m d N (s+(q+4))
    (Packet (s+(q+4))) c cT (1+Forward (s+(q+4))) Tinv Tinv' hInv
  rw [hP _ le_rfl,hF _ le_rfl] at hMg
  unfold finiteOriginalMeanSizeCost
  simp only [hP _ le_rfl,hF _ le_rfl,hMeta,hBnd,hMg]
  apply fullIncrementNovMeanNormCost_prefix_congr
  intro k hk
  exact parameterRound2_identityRawTransition_prefix_congr m d (s+1)
    Packet Packet' Forward Forward' (fun k hk => hP k (by omega))
    (fun k hk => hF k (by omega)) k hk

/-- All four profile tails above `(q+1)*(q+4)+2` leave the exact entrance
threshold unchanged. In particular a later derivative order never enters it. -/
theorem finiteOriginalMeanThreshold_prefix_congr
    (q Rsub Lprimary : ℕ) (rho c cT : ℝ) (hrho : 0 < rho)
    (Packet Forward Meta Tinv Packet' Forward' Meta' Tinv' : ℕ → ℝ)
    (hPacket : ∀ k, 0 ≤ Packet k) (hForward : ∀ k, 0 ≤ Forward k)
    (hPacket' : ∀ k, 0 ≤ Packet' k) (hForward' : ∀ k, 0 ≤ Forward' k)
    (hP : ∀ k, k ≤ (q+1)*(q+4)+2 → Packet k = Packet' k)
    (hF : ∀ k, k ≤ (q+1)*(q+4)+2 → Forward k = Forward' k)
    (hMeta : ∀ k, k ≤ (q+1)*(q+4)+2 → Meta k = Meta' k)
    (hInv : ∀ k, k ≤ (q+1)*(q+4)+2 → Tinv k = Tinv' k) :
    finiteOriginalMeanThreshold.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lprimary rho c cT hrho Packet Forward Meta Tinv hPacket hForward =
    finiteOriginalMeanThreshold.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lprimary rho c cT hrho Packet' Forward' Meta' Tinv' hPacket' hForward' := by
  unfold finiteOriginalMeanThreshold
  rw [hP 0 (Nat.zero_le _)]
  apply parameterRound2_uniformMeanThreshold_all_prefix_congr
  · intro k hk
    apply hP k
    rw [Nat.add_mul,Nat.one_mul]
    omega
  · intro s hs R
    apply finiteOriginalMeanSizeCost_prefix_congr
    · intro k hk
      apply hP k
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · intro k hk
      apply hF k
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · apply hMeta
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · intro k hk
      apply hInv k
      rw [Nat.add_mul,Nat.one_mul]
      omega

end GlobalEmbedding.Continuation.CollarCompletion
#print axioms GlobalEmbedding.Continuation.CollarCompletion.finiteOriginalMeanSizeCost_prefix_congr
#print axioms GlobalEmbedding.Continuation.CollarCompletion.finiteOriginalMeanThreshold_prefix_congr
