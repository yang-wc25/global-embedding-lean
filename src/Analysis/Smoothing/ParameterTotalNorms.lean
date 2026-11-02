import Smoothing.ParameterOriginalABI
import GlobalEmbedding.Offline.BufferedOriginalEuclidean
import GlobalEmbedding.Offline.BufferedWeightedGain

/-!
# Literal total-joint base-two map norms in the frozen original ABI

The frozen CoreInputProfile uses paperAtlasWeighted 2. Unlike the separate
spatial-packet norm, this includes pure parameter derivatives of orders j+1
and j+2. These exact bridges retain that stronger, unchanged norm and the
same actual Euclidean-valued map. No norm definition is modified.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d q : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]
variable (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
local notation "c" => parameterTensorModelEquiv n d
local notation "cy" => EuclideanSpace.equiv (Fin q) ℝ
local notation "AB" => parameterProductAtlas A B

theorem parameterTotalMap_Cj_eq_original
    (u : P × M → EuclideanSpace ℝ (Fin q)) (j : ℕ)
    (S : Fin (B.count*A.count) → Set (Fin (n+d) → ℝ)) :
    paperAtlasCj j (bufferedModelCoordinates AB c (cy ∘ u)) (bufferedModelTargets AB c) S =
    paperAtlasCj j (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (fun i => S (parameterTensorAtlasIndex A B i)) := by
  erw [← paperAtlasCj_reindex (parameterTensorAtlasIndex A B)]
  have hf : (fun i => bufferedModelCoordinates AB c (cy ∘ u) (parameterTensorAtlasIndex A B i)) =
      incrementsOriginalMapCoordinates A B.chart u := by
    funext i y
    exact parameterBufferedModelCoordinates_eq_original A B u i y
  rw [hf]
  congr 1
  exact funext (parameterTensorModel_targets A B)

theorem parameterTotalMap_weighted_eq_original
    (u : P × M → EuclideanSpace ℝ (Fin q)) (base m : ℕ) (t : ℝ)
    (S : Fin (B.count*A.count) → Set (Fin (n+d) → ℝ)) :
    paperAtlasWeighted base m t (bufferedModelCoordinates AB c (cy ∘ u)) (bufferedModelTargets AB c) S =
    paperAtlasWeighted base m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (fun i => S (parameterTensorAtlasIndex A B i)) := by
  unfold paperAtlasWeighted
  apply Finset.sum_congr rfl
  intro j _
  rw [parameterTotalMap_Cj_eq_original]

/-- Exact original output norm, including every pure parameter derivative. -/
theorem parameterTotalMap_weighted_inner_eq_original
    (u : P × M → EuclideanSpace ℝ (Fin q)) (base m : ℕ) (t : ℝ) :
    paperAtlasWeighted base m t (bufferedModelCoordinates AB c (cy ∘ u))
      (bufferedModelTargets AB c) (bufferedModelInner AB c) =
    paperAtlasWeighted base m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalInner A B) := by
  erw [parameterTotalMap_weighted_eq_original A B u base m t]
  congr 1
  exact funext (parameterTensorModel_inner A B)

theorem parameterTotalMap_Cj_sampling_le_original
    (u : P × M → EuclideanSpace ℝ (Fin q)) (j : ℕ) :
    paperAtlasCj j (bufferedModelCoordinates AB c (cy ∘ u))
      (bufferedModelTargets AB c) (bufferedModelSampling AB c) ≤
    paperAtlasCj j (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) := by
  erw [parameterTotalMap_Cj_eq_original A B u j]
  exact paperAtlasCj_mono_evaluation _ _ _ _ _ (parameterTensorModel_sampling_subset A B)

theorem parameterTotalMap_weighted_sampling_le_original
    (u : P × M → EuclideanSpace ℝ (Fin q)) (base m : ℕ) (t : ℝ) :
    paperAtlasWeighted base m t (bufferedModelCoordinates AB c (cy ∘ u))
      (bufferedModelTargets AB c) (bufferedModelSampling AB c) ≤
    paperAtlasWeighted base m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) := by
  erw [parameterTotalMap_weighted_eq_original A B u base m t]
  exact paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ (parameterTensorModel_sampling_subset A B)

#print axioms parameterTotalMap_weighted_inner_eq_original
#print axioms parameterTotalMap_weighted_sampling_le_original
end
end GlobalEmbedding.Continuation
