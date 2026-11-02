import OriginalIncrements.FiniteLowPhasePreparation
import OriginalIncrements.OriginalPhysicalPhaseJets

/-! The original noncriticality and the actual finite two-entry phase budget
manufacture a prepared compact phase with an explicit low-order constant. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.OriginalIncrements

def originalLowPhaseBudget (m d : ℕ) (Packet : ℕ → ℝ) : ℝ :=
  max 0 (max (actualOriginalTotalPhaseJetCost (m+1) d 0*Packet 0+1)
    (actualOriginalTotalPhaseJetCost (m+1) d 1*Packet 1+1))+1

theorem originalLowPhaseBudget_pos (m d : ℕ) (Packet : ℕ → ℝ) :
    0 < originalLowPhaseBudget m d Packet := by
  exact add_pos_of_nonneg_of_pos (le_max_left _ _) zero_lt_one

theorem originalLowPhaseBudget_prefix_congr (m d : ℕ) (P Q : ℕ → ℝ)
    (h : ∀ k ≤ 1, P k = Q k) : originalLowPhaseBudget m d P = originalLowPhaseBudget m d Q := by
  simp only [originalLowPhaseBudget,h 0 (by omega),h 1 le_rfl]

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem original_primary_phase_preparation_from_finite_low_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUprim : U ⊆ actualOriginalPrimaryNativeOpen Data nu i)
    (ell : ℝ) (hell : 0 < ell) (Packet : ℕ → ℝ)
    (hLow : ∀ k, k ≤ 1 → ∀ x ∈ K,
      ell^k*‖iteratedFDeriv ℝ (k+1) (originalNativePrimaryPhase Data nu i) x‖ ≤
        actualOriginalTotalPhaseJetCost (m+1) d k*Packet k+1) :
    ∃ (mu R rho : ℝ) (O : Set X),
      0 < mu ∧ 0 < R ∧ 0 < rho ∧ rho ≤ ell ∧
      IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧ K ⊆ closedBall 0 R ∧
      (∀ x ∈ K, ball x rho ⊆ O) ∧ ContDiffOn ℝ ∞ (originalNativePrimaryPhase Data nu i) O ∧
      (∀ x ∈ K, mu ≤ ‖(fderiv ℝ (originalNativePrimaryPhase Data nu i) x).comp
        (ContinuousLinearMap.inr ℝ Ep D)‖) ∧
      (∀ x ∈ O, ‖fderiv ℝ (originalNativePrimaryPhase Data nu i) x‖ ≤ originalLowPhaseBudget m d Packet) ∧
      (∀ x ∈ O, rho*‖iteratedFDeriv ℝ 2 (originalNativePrimaryPhase Data nu i) x‖ ≤
        originalLowPhaseBudget m d Packet) := by
  have hpsi : ContDiffOn ℝ ∞ (originalNativePrimaryPhase Data nu i) U :=
    (round3_actual_original_primary_native_phase_smooth Data hd hs nu i).mono hUprim
  have hNonzero : ∀ z ∈ K,
      (fderiv ℝ (originalNativePrimaryPhase Data nu i) z).comp (ContinuousLinearMap.inr ℝ Ep D) ≠ 0 := by
    intro z hz
    have hactive := round3_prepared_native_primary_active Data i nu (hUprim (hKU hz))
    have hgood := hp.primary_good nu _ hactive
    have ht : z.2 ∈ (Data.atlas.chart i.1).target := by
      have hh := (hUprim (hKU hz)).1.1.1
      have he := congrArg Prod.snd ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
      change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z) = z.2 at he
      rwa [he] at hh
    exact round3_actual_host_phase_spatial_ne_zero (Data.atlas.chart i.1)
      (hd.atlas_smooth.chart_mem i.1)
      (fun w : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm w.1,w.2)) z ht
      ((hpsi.contDiffAt (hU.mem_nhds (hKU hz))).differentiableAt (by simp)) hgood.1
  apply compact_phase_preparation_from_finite_low_jets
    (originalNativePrimaryPhase Data nu i) K U hK hU hKU hpsi hNonzero ell
    (actualOriginalTotalPhaseJetCost (m+1) d 0*Packet 0+1)
    (actualOriginalTotalPhaseJetCost (m+1) d 1*Packet 1+1) hell
  · intro x hx
    simpa [norm_iteratedFDeriv_one] using hLow 0 (by omega) x hx
  · intro x hx
    simpa only [pow_one] using hLow 1 le_rfl x hx

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_primary_phase_preparation_from_finite_low_jets
