import OriginalCollars.ActualSampledPhaseControls
import OriginalIncrements.FiniteRefinementObserverBudget
import Probes.ActualIncrementOriginalSignedPhaseJets
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

def signedPhaseFromGivenBudget (m d : ℕ) (Packet : ℕ → ℝ) (k : ℕ) : ℝ :=
  2*phaseFromGivenBudget m d Packet k

theorem signedPhaseFromGivenBudget_nonneg (m d : ℕ) (Packet : ℕ → ℝ) (k : ℕ) :
    0 ≤ signedPhaseFromGivenBudget m d Packet k :=
  mul_nonneg (by norm_num) (phaseFromGivenBudget_nonneg m d Packet k)

theorem original_signed_native_positive_jets_at
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (owner : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (mu Mb : ℝ) (hmu : 0 < mu) (hMb : 0 ≤ Mb)
    (native : OpenPartialHomeomorph X X)
    (controls : ActualPhaseSampleJetControls mu Mb
      ((actualOriginalParameterSignedPhase Data owner r.val) ∘
        (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart owner.1)).symm) native)
    (point : X) (hPoint : point ∈ native.source)
    (hOwnNu : parameterTensorModelEquiv (m+1) d point ∈ incrementsOriginalPrimaryEvaluation Data r.val.1.1 owner)
    (hOwnMu : parameterTensorModelEquiv (m+1) d point ∈ incrementsOriginalPrimaryEvaluation Data r.val.1.2 owner)
    (Packet : ℕ → ℝ) (ell : ℝ) (hell : 0 < ell) (j : ℕ)
    (hFinite : ∀ k, k ≤ j-1 → actualOriginalGivenInputProfile Data k ell ≠ ⊤)
    (hBudget : ∀ k, k ≤ j-1 → (actualOriginalGivenInputProfile Data k ell).toReal ≤ Packet k) :
    ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k native point‖ ≤
        phaseForwardBudget Mb (signedPhaseFromGivenBudget m d Packet) k ∧
      ell^(k-1)*‖iteratedFDeriv ℝ k native.symm (native point)‖ ≤
        phaseInverseBudget mu Mb (signedPhaseFromGivenBudget m d Packet) k := by
  have hFirst := controls.first
  have hHigher := controls.higher
  have hInverse := controls.inverse
  let Phase := signedPhaseFromGivenBudget m d Packet
  let psi := (actualOriginalParameterSignedPhase Data owner r.val) ∘
    (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart owner.1)).symm
  have hIdentity : psi = fun y : X =>
      actualOriginalParameterSignedPhase Data owner ((r.val.1.1,r.val.1.2),r.val.2)
        (y.1,(Data.atlas.chart owner.1).symm y.2) := by
    funext y
    rfl
  have hPhase : ∀ k, 1 ≤ k → 0 ≤ Phase k := fun k _ => signedPhaseFromGivenBudget_nonneg m d Packet k
  have hPhaseJets (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) :
      ell^(k-1)*‖iteratedFDeriv ℝ k psi point‖ ≤ Phase k := by
    have hh := actual_original_given_signed_phase_positive_jets Data hd hs (k-1) ell
      (max 0 (Packet (k-1))) hell (hFinite (k-1) (by omega))
      ((hBudget (k-1) (by omega)).trans (le_max_right _ _))
      r.val.1.1 r.val.1.2 r.val.2 owner (k-1) le_rfl point hOwnNu hOwnMu
    dsimp only at hh
    rw [Nat.sub_add_cancel hk,← hIdentity] at hh
    simpa only [Phase,signedPhaseFromGivenBudget,phaseFromGivenBudget,
      ite_eq_right (show k ≠ 0 by omega)] using hh
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
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_signed_native_positive_jets_at
