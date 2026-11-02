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

theorem round4_original_C3_native_joint_jets
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (F : P × M → V)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hCoords : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i))
    (R3 : ℝ) (hR3 : 0 ≤ R3)
    (hC3 : paperAtlasCj 3 (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≤ ENNReal.ofReal R3)
    (i : Fin A.count × Fin c) (k : ℕ) (hk : k ≤ 3) (z : X)
    (hz : parameterTensorModelEquiv n d z ∈ S i) :
    ‖iteratedFDeriv ℝ k (round3OriginalNativeMapCoordinates A B F i) z‖ ≤
      actualOriginalMapJetCost n d N 1*R3 := by
  have hFinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hC3
  have hReal : (paperAtlasCj 3 (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ R3 := by
    simpa only [ENNReal.toReal_ofReal hR3] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hC3
  have hWeighted : paperAtlasWeighted 3 0 1 (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ := by
    simpa only [paperAtlasWeighted,Finset.sum_range_one,pow_zero,zero_add,one_mul] using hFinite
  have h := paperAtlasWeighted_native_shifted_joint_jet_le
    (parameterTensorModelEquiv n d) (EuclideanSpace.equiv (Fin N) ℝ).symm
    3 0 1 zero_lt_one (incrementsOriginalMapCoordinates A B F)
    (incrementsOriginalDifferentiation A B) S
    (parameterRound2_originalDifferentiation_open A B) hSO hCoords hWeighted i (k := 0) (b := k)
    le_rfl hk hz
  rw [← round3_original_native_map_coordinates_eq] at h
  simp only [zero_add,pow_zero,one_mul,paperAtlasWeighted,Finset.sum_range_one] at h
  convert h.trans (mul_le_mul_of_nonneg_left hReal (actualOriginalMapJetCost_nonneg n d N 1)) using 1
  · interval_cases k <;> rfl
  · rfl

theorem round4_original_native_host_joint_smooth
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (F : P × M → V)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hCoords : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i)
      (incrementsOriginalDifferentiation A B i))
    (i : Fin A.count × Fin c) (W : Set X)
    (hSample : ∀ z ∈ W, parameterTensorModelEquiv n d z ∈ S i) :
    ContDiffOn ℝ ∞ (round3OriginalNativeMapCoordinates A B F i) W := by
  rw [round3_original_native_map_coordinates_eq]
  exact (EuclideanSpace.equiv (Fin N) ℝ).symm.contDiff.comp_contDiffOn
    ((hCoords i).comp (parameterTensorModelEquiv n d).contDiff.contDiffOn
      (fun z hz => hSO i (hSample z hz)))

theorem round4_original_native_host_target
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (i : Fin A.count × Fin c) (z : X)
    (hSample : parameterTensorModelEquiv n d z ∈ S i) :
    z.2 ∈ (A.chart i.1).target := by
  have h := (hSO i hSample).1
  have hx := congrArg Prod.snd ((parameterTensorModelEquiv n d).symm_apply_apply z)
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z) = z.2 at hx
  simpa only [hx] using h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_original_C3_native_joint_jets
#print axioms GlobalEmbedding.Continuation.round4_original_native_host_joint_smooth
#print axioms GlobalEmbedding.Continuation.round4_original_native_host_target
