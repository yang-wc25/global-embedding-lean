import OriginalIncrements.OriginalFinitePrimarySupply
import IncrementsCompletion.OriginalPhasePositiveSupply
import Probes.ActualIncrementOriginalSampling

/-! Actual native positive jets of the same finite primary packet, with
explicit original Given-prefix costs. This bridge is used by the conditioned
observer profile proof, whose charts retain these exact native functions. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

theorem original_budgeted_native_positive_jets_at
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalBudgetedPrimarySupply Data theta)
    (nu : Fin Data.primaryCount) (owner : Fin Data.atlas.count × Fin Data.parameterCount)
    (a : supply.packet.s nu owner) (point : X)
    (hPoint : point ∈ (supply.packet.piece nu owner a).native.source)
    (hOwnSample : parameterTensorModelEquiv (m+1) d point ∈ incrementsOriginalPrimaryEvaluation Data nu owner)
    (Packet : ℕ → ℝ) (ell : ℝ) (hell : 0 < ell) (j : ℕ)
    (hFinite : ∀ k, k ≤ j-1 → actualOriginalGivenInputProfile Data k ell ≠ ⊤)
    (hBudget : ∀ k, k ≤ j-1 → (actualOriginalGivenInputProfile Data k ell).toReal ≤ Packet k) :
    ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k (supply.packet.piece nu owner a).native point‖ ≤
        phaseForwardBudget (supply.Mb nu owner) (phaseFromGivenBudget m d Packet) k ∧
      ell^(k-1)*‖iteratedFDeriv ℝ k (supply.packet.piece nu owner a).native.symm
        ((supply.packet.piece nu owner a).native point)‖ ≤
        phaseInverseBudget (supply.mu nu owner) (supply.Mb nu owner) (phaseFromGivenBudget m d Packet) k := by
  let native := (supply.packet.piece nu owner a).native
  let mu := supply.mu nu owner
  let Mb := supply.Mb nu owner
  have hmu : 0 < mu := supply.mu_pos nu owner
  have hMb : 0 ≤ Mb := supply.Mb_nonneg nu owner
  have hFirst := supply.native_first nu owner a
  have hHigher := supply.native_higher nu owner a
  have hInverse := supply.native_inverse nu owner a
  let Phase := phaseFromGivenBudget m d Packet
  let psi := (fun z : Ep × M => Data.phase nu ((Data.parameterChart owner.2).symm z.1,z.2)) ∘
    (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart owner.1)).symm
  have hPhase : ∀ k, 1 ≤ k → 0 ≤ Phase k := fun k _ => phaseFromGivenBudget_nonneg m d Packet k
  have hIdentity : psi = actualOriginalJointPhase Data nu owner ∘ parameterTensorModelEquiv (m+1) d := by
    funext x
    simp only [Function.comp_apply,actualOriginalJointPhase,actual_original_jointPoint_native]
    rfl
  have hPhaseJets (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) :
      ell^(k-1)*‖iteratedFDeriv ℝ k psi point‖ ≤ Phase k := by
    have hh := actual_original_given_phase_positive_jets Data hd hs (k-1) ell
      (max 0 (Packet (k-1))) hell (hFinite (k-1) (by omega))
      ((hBudget (k-1) (by omega)).trans (le_max_right _ _)) nu owner
      (k-1) le_rfl point hOwnSample
    rw [Nat.sub_add_cancel hk,← hIdentity] at hh
    simpa only [Phase,phaseFromGivenBudget,ite_eq_right (show k ≠ 0 by omega)] using hh
  intro k hk hkj
  constructor
  · by_cases hk1 : k = 1
    · subst k
      simpa [phaseForwardBudget,norm_iteratedFDeriv_one] using hFirst point hPoint
    · have hh := hHigher (k-1) (by omega) point hPoint
      rw [Nat.sub_add_cancel hk,show k-1+2 = k+1 by omega] at hh
      calc
        _ ≤ ell^(k-1)*(2^(k+1)*‖iteratedFDeriv ℝ k psi point‖) :=
          mul_le_mul_of_nonneg_left hh (pow_nonneg hell.le _)
        _ = 2^(k+1)*(ell^(k-1)*‖iteratedFDeriv ℝ k psi point‖) := by ring
        _ ≤ 2^(k+1)*Phase k := mul_le_mul_of_nonneg_left (hPhaseJets k hk hkj) (by positivity)
        _ = _ := by simp only [phaseForwardBudget,ite_eq_right (show k ≠ 0 by omega),ite_eq_right hk1,Phase]
  · let S : Set X := {native point}
    have hS : S ⊆ native.target := singleton_subset_iff.mpr (native.map_source hPoint)
    have hPrefix0 : 0 ≤ bufferedTransitionPrefix (incrementsCompletionPositiveSlots Phase) k :=
      zero_le_one.trans (one_le_bufferedTransitionPrefix
        (incrementsCompletionPositiveSlots_nonneg Phase hPhase) k)
    have hh := hInverse S hS (k-1) ell
      (bufferedTransitionPrefix (incrementsCompletionPositiveSlots Phase) k) hell hPrefix0
      (by
        intro l hl hlk x hx
        obtain ⟨y,hy,rfl⟩ := hx
        have hyEq : y = native point := mem_singleton_iff.mp hy
        rw [hyEq,native.left_inv hPoint]
        have hlj : l+1 ≤ j := by omega
        have hp := hPhaseJets (l+1) (by omega) hlj
        simp only [Nat.add_sub_cancel] at hp
        exact hp.trans (phase_positive_prefix_bound Phase hPhase (by omega) (by omega)))
      k hk (by omega) (native point) (mem_singleton _)
    simpa only [phaseInverseBudget,ite_eq_right (show k ≠ 0 by omega)] using hh

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_budgeted_native_positive_jets_at
