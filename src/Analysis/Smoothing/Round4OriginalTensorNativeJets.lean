import Smoothing.Round4OriginalNativeTensor
import Smoothing.Round4OriginalC3NativeJets

/-! The original tensor seminorm, on the unchanged original samples, supplies
all native joint tensor jets. The fixed reconstruction map and model change
are the only costs; no atlas count or separate native tensor budget enters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation

private local instance nativeTensorNormed (n : ℕ) :
    NormedAddCommGroup ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := inferInstance
private local instance nativeTensorSpace (n : ℕ) :
    NormedSpace ℝ ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) := inferInstance

def round4OriginalTensorJetCost (n d j : ℕ) : ℝ :=
  ‖round4NativeTensorFromCoordinates n‖ *
    (‖(ContinuousLinearEquiv.refl ℝ (Fin (n*n) → ℝ)).toContinuousLinearMap‖ *
      linearModelFactor (parameterTensorModelEquiv n d) j * coordinateDimensionFactor (n+d) j)

theorem round4OriginalTensorJetCost_nonneg (n d j : ℕ) :
    0 ≤ round4OriginalTensorJetCost n d j :=
  mul_nonneg (norm_nonneg _) (mul_nonneg
    (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _)) (coordinateDimensionFactor_nonneg _ _))

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "X" => (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin n))
local notation "𝓙" => 𝓘(ℝ,EuclideanSpace ℝ (Fin n))

theorem round4_original_tensor_native_jets
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : Fin c → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (hCoords : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B T i)
      (incrementsOriginalDifferentiation A B i))
    (j : ℕ) (Rj : ℝ) (hRj : 0 ≤ Rj)
    (hCj : paperAtlasCj j (incrementsOriginalTensorCoordinates A B T)
      (incrementsOriginalDifferentiation A B) S ≤ ENNReal.ofReal Rj)
    (i : Fin A.count × Fin c) (W : Set X) (hW : IsOpen W)
    (hSample : ∀ z ∈ W, parameterTensorModelEquiv n d z ∈ S i) :
    ContDiffOn ℝ ∞ (round4OriginalNativeTensorCoordinates A B T i) W ∧
    ∀ k ≤ j, ∀ z ∈ W, ‖iteratedFDeriv ℝ k (round4OriginalNativeTensorCoordinates A B T i) z‖ ≤
      round4OriginalTensorJetCost n d j * Rj := by
  let f := incrementsOriginalTensorCoordinates A B T i ∘ parameterTensorModelEquiv n d
  have hf : ContDiffOn ℝ ∞ f W :=
    (hCoords i).comp (parameterTensorModelEquiv n d).contDiff.contDiffOn
      (fun z hz => hSO i (hSample z hz))
  refine ⟨(round4NativeTensorFromCoordinates n).contDiff.comp_contDiffOn hf,?_⟩
  intro k hk z hz
  have hFinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hCj
  have hReal : (paperAtlasCj j (incrementsOriginalTensorCoordinates A B T)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ Rj := by
    simpa only [ENNReal.toReal_ofReal hRj] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hCj
  have hWeighted : paperAtlasWeighted j 0 1 (incrementsOriginalTensorCoordinates A B T)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ := by
    simpa only [paperAtlasWeighted,Finset.sum_range_one,pow_zero,zero_add,one_mul] using hFinite
  let C := ‖(ContinuousLinearEquiv.refl ℝ (Fin (n*n) → ℝ)).toContinuousLinearMap‖ *
    linearModelFactor (parameterTensorModelEquiv n d) j * coordinateDimensionFactor (n+d) j
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _)) (coordinateDimensionFactor_nonneg _ _)
  have h := paperAtlasWeighted_native_shifted_joint_jet_le
    (parameterTensorModelEquiv n d) (ContinuousLinearEquiv.refl ℝ (Fin (n*n) → ℝ))
    j 0 1 zero_lt_one (incrementsOriginalTensorCoordinates A B T)
    (incrementsOriginalDifferentiation A B) S
    (parameterRound2_originalDifferentiation_open A B) hSO hCoords hWeighted i (k := 0) (b := k)
    le_rfl hk (hSample z hz)
  simp only [zero_add,pow_zero,one_mul,paperAtlasWeighted,Finset.sum_range_one] at h
  have hCoeff : ‖iteratedFDeriv ℝ k f z‖ ≤ C*Rj := by
    convert h.trans (mul_le_mul_of_nonneg_left hReal hC) using 1
    exact congrArg (fun q : ℕ => ‖iteratedFDeriv ℝ q f z‖) (Nat.zero_add k).symm
  have hPost := (round4NativeTensorFromCoordinates n).norm_iteratedFDeriv_comp_left
    (hf.contDiffAt (hW.mem_nhds hz)) (by simp : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  calc
    _ ≤ ‖round4NativeTensorFromCoordinates n‖ * ‖iteratedFDeriv ℝ k f z‖ := hPost
    _ ≤ ‖round4NativeTensorFromCoordinates n‖ * (C*Rj) :=
      mul_le_mul_of_nonneg_left hCoeff (norm_nonneg _)
    _ = round4OriginalTensorJetCost n d j*Rj := by dsimp [C,round4OriginalTensorJetCost]; ring

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_original_tensor_native_jets
