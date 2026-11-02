import Smoothing.ParameterRound2OriginalFixedPacket
import Probes.ActualOriginalTransitionProfileJets

/-! Actual original coordinate transition jets are controlled by the
fixed packet, independently of the current map and metric tensor. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "X" => Ep × Es

theorem round3_original_fixed_transition_positive_jets
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (j : ℕ) (ell budget : ℝ) (hell : 0 < ell)
    (hfinite : parameterRound2_originalFixedPacketProfile D j ell ≠ ⊤)
    (hbudget : (parameterRound2_originalFixedPacketProfile D j ell).toReal ≤ budget)
    (ik : (Fin D.atlas.count × Fin D.parameterCount) ×
      (Fin D.atlas.count × Fin D.parameterCount))
    (k : ℕ) (hk : k ≤ j) (z : Fin (n+d) → ℝ)
    (hz : z ∈ actualOriginalGivenTransitionSample D ik) :
    ell^k*‖iteratedFDeriv ℝ (k+1) (actualOriginalGivenTransition D ik.1 ik.2) z‖ ≤
      actualOriginalGivenTransitionJetCost n d j*budget := by
  let O := actualOriginalGivenTransitionDomain D
  let S := actualOriginalGivenTransitionSample D
  let f := actualOriginalGivenTransitionDifferentialCoordinates D
  have hO := actualOriginalGivenTransitionDomain_open D
  have hSO : ∀ i, S i ⊆ O i := fun _ => inter_subset_right
  have hf := actualOriginalGivenTransitionDifferential_contDiffOn D hd
  have hle := show paperAtlasWeighted 0 j ell (actualOriginalGivenTransitionDifferentialCoordinates D)
      (actualOriginalGivenTransitionDomain D) (actualOriginalGivenTransitionSample D) ≤
      parameterRound2_originalFixedPacketProfile D j ell from
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hfin : paperAtlasWeighted 0 j ell f O S ≠ ⊤ := ne_top_of_le_ne_top hfinite hle
  have hbound : (paperAtlasWeighted 0 j ell f O S).toReal ≤ budget :=
    (ENNReal.toReal_mono hfinite hle).trans hbudget
  have hj := paperAtlasWeighted_shifted_joint_jet_le 0 j ell hell f O S hO hSO hf hfin ik hk
    (le_refl 0) hz
  simp only [Nat.add_zero] at hj
  have hcoef : ell^k*‖iteratedFDeriv ℝ k (f ik) z‖ ≤ coordinateDimensionFactor (n+d) j*budget :=
    hj.trans (mul_le_mul_of_nonneg_left hbound (coordinateDimensionFactor_nonneg _ _))
  have hDf : fderiv ℝ (actualOriginalGivenTransition D ik.1 ik.2) =
      actualMatrixOperatorAssembly (n+d) ∘ f ik := by
    funext y
    exact (actualMatrixOperatorAssembly_exact (n+d)
      (fderiv ℝ (actualOriginalGivenTransition D ik.1 ik.2) y)).symm
  have hp := slow_linear_jet_bound (actualMatrixOperatorAssembly (n+d)) (O ik) (hO ik) (f ik) (hf ik)
    k ell (coordinateDimensionFactor (n+d) j*budget) hell.le z (hSO ik hz) hcoef
  rw [← hDf,norm_iteratedFDeriv_fderiv] at hp
  exact hp.trans_eq (by dsimp only [actualOriginalGivenTransitionJetCost]; ring)

#print axioms round3_original_fixed_transition_positive_jets
end GlobalEmbedding.Continuation
