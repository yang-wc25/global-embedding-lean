import Smoothing.Round3OuterC2NativeJets

/-! The unchanged original paper C3 seminorm bounds every native joint
derivative through order three, with its exact fixed model comparison.
The sampling set is retained; no atlas cardinality enters the constant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem round4_original_finite_native_joint_jets
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (F : P × M → V)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hCoords : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i))
    (j : ℕ) (Rj : ℝ) (hRj : 0 ≤ Rj)
    (hCj : paperAtlasCj (j+2) (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≤ ENNReal.ofReal Rj)
    (i : Fin A.count × Fin c) (k : ℕ) (hk : k ≤ j+2) (z : X)
    (hz : parameterTensorModelEquiv n d z ∈ S i) :
    ‖iteratedFDeriv ℝ k (round3OriginalNativeMapCoordinates A B F i) z‖ ≤
      actualOriginalMapJetCost n d N j*Rj := by
  have hFinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hCj
  have hReal : (paperAtlasCj (j+2) (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ Rj := by
    simpa only [ENNReal.toReal_ofReal hRj] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hCj
  have hWeighted : paperAtlasWeighted (j+2) 0 1 (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ := by
    simpa only [paperAtlasWeighted,Finset.sum_range_one,pow_zero,zero_add,one_mul] using hFinite
  have h := paperAtlasWeighted_native_shifted_joint_jet_le
    (parameterTensorModelEquiv n d) (EuclideanSpace.equiv (Fin N) ℝ).symm
    (j+2) 0 1 zero_lt_one (incrementsOriginalMapCoordinates A B F)
    (incrementsOriginalDifferentiation A B) S
    (parameterRound2_originalDifferentiation_open A B) hSO hCoords hWeighted i (k := 0) (b := k)
    le_rfl hk hz
  rw [← round3_original_native_map_coordinates_eq] at h
  simp only [zero_add,pow_zero,one_mul,paperAtlasWeighted,Finset.sum_range_one] at h
  convert h.trans (mul_le_mul_of_nonneg_left hReal (actualOriginalMapJetCost_nonneg n d N j)) using 1
  · exact congrArg (fun q : ℕ => ‖iteratedFDeriv ℝ q (round3OriginalNativeMapCoordinates A B F i) z‖)
      (Nat.zero_add k).symm
  · rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_original_finite_native_joint_jets
