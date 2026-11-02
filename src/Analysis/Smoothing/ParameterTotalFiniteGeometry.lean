import Smoothing.ParameterPreparedTotalPair
import Smoothing.ParameterFiniteGeometry

/-!
# Finite-prefix audit of the literal total-joint original (6.4) constant

At output order m, the map's exact base-two constant reads B,T only through
m+2, while the tensor reads B through m and T through m+1. The fixed repair
choice r=q=40*(k+1) changes the kernel and source norm, not these geometric
orders. The theorem below proves equality of the actual maximum constant.
-/

open GlobalEmbedding.Offline MeasureTheory
open scoped BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

theorem parameterBufferedTransferConstant_congr_prefix
    {B₁ B₂ T₁ T₂ : ℕ → ℝ} (D j : ℕ)
    (hB : ∀ a ≤ j, B₁ a = B₂ a) (hT : ∀ a ≤ j, T₁ a = T₂ a) :
    bufferedTransferConstant B₁ T₁ D j = bufferedTransferConstant B₂ T₂ D j := by
  change parameterJetTransferConstant (bufferedCutoffSquareConstant B₁) T₁ D j =
    parameterJetTransferConstant (bufferedCutoffSquareConstant B₂) T₂ D j
  exact parameterJetTransferConstant_congr_prefix D j
    (fun a ha => parameterCutoffSquareConstant_congr_prefix a (fun b hb => hB b (hb.trans ha))) hT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {d : ℕ}

theorem parameterTotalMapTailConstant_congr_prefix
    (c : E ≃L[ℝ] (Fin d → ℝ)) (mu : Measure E) (kappa : E → ℝ)
    {B₁ B₂ T₁ T₂ : ℕ → ℝ} (D m r : ℕ)
    (hB : ∀ a ≤ m+2, B₁ a = B₂ a) (hT : ∀ a ≤ m+2, T₁ a = T₂ a) :
    modelBufferedSmoothingTailConstant c mu kappa B₁ T₁ D 2 m r =
    modelBufferedSmoothingTailConstant c mu kappa B₂ T₂ D 2 m r := by
  unfold modelBufferedSmoothingTailConstant modelBufferedTransferConstant
  rw [parameterBufferedTransferConstant_congr_prefix D (m+2) hB hT]

theorem parameterTotalMapGainConstant_congr_prefix
    (c : E ≃L[ℝ] (Fin d → ℝ)) (mu : Measure E) (K : E → ℝ)
    {B₁ B₂ T₁ T₂ : ℕ → ℝ} (D m : ℕ)
    (hB : ∀ a ≤ m+2, B₁ a = B₂ a) (hT : ∀ a ≤ m+2, T₁ a = T₂ a) :
    modelBufferedSmoothingGainConstant c mu K B₁ T₁ D 2 m =
    modelBufferedSmoothingGainConstant c mu K B₂ T₂ D 2 m := by
  unfold modelBufferedSmoothingGainConstant
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by simpa using hj
  unfold modelBufferedTransferConstant
  rw [parameterBufferedTransferConstant_congr_prefix D (j+2)
    (fun a ha => hB a (by omega)) (fun a ha => hT a (by omega))]

/-- The exact single constant in ParameterPreparedTotalPair has this finite
normalized-geometry dependency; no derivative past m+2 can alter its value. -/
theorem parameterTotalPairTailConstant_congr_prefix
    (n : ℕ) (c : E ≃L[ℝ] (Fin d → ℝ)) (mu : Measure E) (kappa : E → ℝ)
    {B₁ B₂ T₁ T₂ : ℕ → ℝ} (D m r : ℕ)
    (hB : ∀ a ≤ m+2, B₁ a = B₂ a) (hT : ∀ a ≤ m+2, T₁ a = T₂ a) :
    max (modelBufferedSmoothingTailConstant c mu kappa B₁ T₁ D 2 m r)
      (modelTensorSmoothingTailConstant n c mu kappa B₁ T₁ (fun j => T₁ (j+1)) D 0 m r) =
    max (modelBufferedSmoothingTailConstant c mu kappa B₂ T₂ D 2 m r)
      (modelTensorSmoothingTailConstant n c mu kappa B₂ T₂ (fun j => T₂ (j+1)) D 0 m r) := by
  rw [parameterTotalMapTailConstant_congr_prefix c mu kappa D m r hB hT,
    parameterTensorTailConstant_congr_prefix n c mu kappa D m r
      (fun a ha => hB a (by omega)) (fun a ha => hT a (by omega))]

#print axioms parameterTotalMapTailConstant_congr_prefix
#print axioms parameterTotalMapGainConstant_congr_prefix
#print axioms parameterTotalPairTailConstant_congr_prefix
end
end GlobalEmbedding.Continuation
