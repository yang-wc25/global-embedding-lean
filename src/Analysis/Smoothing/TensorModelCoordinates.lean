import Smoothing.TensorGlobalJets
import GlobalEmbedding.Offline.BufferedModelCoordinates

/-!
# Original component norms for the actual buffered tensor operator

The model E and its original atlas remain unchanged. Both directions of the
fixed linear model equivalence are retained. Tensor rank enters constants;
the total number of charts does not.
-/

open Module GlobalEmbedding.Paper Function Set Manifold
open scoped ContDiff

namespace GlobalEmbedding.Offline

noncomputable section

section Constants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}

def modelTensorTransferConstant (n : ℕ) (c : E ≃L[ℝ] (Fin d → ℝ))
    (B T J : ℕ → ℝ) (D j : ℕ) : ℝ :=
  linearModelFactor c.symm j * tensorTransferConstant n B T J D j

theorem modelTensorTransferConstant_nonneg (n : ℕ) (c : E ≃L[ℝ] (Fin d → ℝ))
    {B T J : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j)
    (hJ : ∀ j, 0 ≤ J j) (D j : ℕ) :
    0 ≤ modelTensorTransferConstant n c B T J D j :=
  mul_nonneg (linearModelFactor_nonneg _ _) (tensorTransferConstant_nonneg n hB hT hJ D j)

theorem modelTensorTransferConstant_mono (n : ℕ) (c : E ≃L[ℝ] (Fin d → ℝ))
    {B T J : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j)
    (hJ : ∀ j, 0 ≤ J j) (D : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    modelTensorTransferConstant n c B T J D j ≤ modelTensorTransferConstant n c B T J D k :=
  mul_le_mul (linearModelFactor_mono _ hjk) (tensorTransferConstant_mono n hB hT hJ D hjk)
    (tensorTransferConstant_nonneg n hB hT hJ D j) (linearModelFactor_nonneg _ _)

end Constants

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] {d n : ℕ} {V : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]

/-- Each chart uses its own true tensor components. -/
def bufferedTensorNativeCoordinates (A : BufferedAtlas M E)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) :=
  fun i : Fin A.count => tensorCoefficientField A b H i ∘ (A.chart i).symm

/-- Literal ordered n×n tensor coefficients, with the same model-space
coordinate presentation used by the original atlas component norms. -/
def bufferedTensorModelCoordinates (A : BufferedAtlas M E) (c : E ≃L[ℝ] (Fin d → ℝ))
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) :=
  modelCoordinateFamily c (bufferedTensorNativeCoordinates A b H)

theorem bufferedTensorModelCoordinates_contDiffOn (A : BufferedAtlas M E)
    (c : E ≃L[ℝ] (Fin d → ℝ))
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (tensorCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (bufferedTensorModelCoordinates A c b H i) (bufferedModelTargets A c i) :=
  modelCoordinateFamily_contDiffOn c hH i

end

end GlobalEmbedding.Offline
