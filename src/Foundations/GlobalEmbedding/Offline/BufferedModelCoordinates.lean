import GlobalEmbedding.Offline.ModelCoordinateNorms
import GlobalEmbedding.Offline.BufferedSmoothingJets
import GlobalEmbedding.Offline.BufferedSamplingDomains

/-!
# Coordinate presentations of the original buffered atlas model

Source: `main.tex` 234 and 700–720, original source charts and the buffered
smoothing localization. The atlas is not replaced. A fixed genuine linear
equivalence only expresses its model-space vectors in component coordinates.
Both evaluation domains and differentiation domains are actual preimages.
The global smoother continues to integrate in the ORIGINAL normed model.
-/

open GlobalEmbedding.Paper Function Set Manifold IsManifold
open scoped ContDiff

namespace GlobalEmbedding.Offline

noncomputable section

section Constants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}

/-- The actual global localization constant followed by the source-coordinate
chain rule. Its type has no manifold, atlas, cutoff family, or chart-count input. -/
def modelBufferedTransferConstant (c : E ≃L[ℝ] (Fin d → ℝ))
    (B T : ℕ → ℝ) (D j : ℕ) : ℝ :=
  linearModelFactor c.symm j * bufferedTransferConstant B T D j

theorem modelBufferedTransferConstant_nonneg (c : E ≃L[ℝ] (Fin d → ℝ))
    {B T : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D j : ℕ) :
    0 ≤ modelBufferedTransferConstant c B T D j :=
  mul_nonneg (linearModelFactor_nonneg _ _) (bufferedTransferConstant_nonneg hB hT D j)

theorem modelBufferedTransferConstant_mono (c : E ≃L[ℝ] (Fin d → ℝ))
    {B T : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    {j k : ℕ} (hjk : j ≤ k) :
    modelBufferedTransferConstant c B T D j ≤ modelBufferedTransferConstant c B T D k :=
  mul_le_mul (linearModelFactor_mono _ hjk) (bufferedTransferConstant_mono hB hT D hjk)
    (bufferedTransferConstant_nonneg hB hT D j) (linearModelFactor_nonneg _ _)

end Constants

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] {d q : ℕ}

/-- Native chart representatives, retaining the original model and atlas. -/
def bufferedNativeCoordinates (A : BufferedAtlas M E) (u : M → Fin q → ℝ) :=
  fun i : Fin A.count => u ∘ (A.chart i).symm

/-- Literal component coordinates of the same original chart representatives. -/
def bufferedModelCoordinates (A : BufferedAtlas M E) (c : E ≃L[ℝ] (Fin d → ℝ))
    (u : M → Fin q → ℝ) := modelCoordinateFamily c (bufferedNativeCoordinates A u)

/-- Original differentiation chart targets expressed in component coordinates. -/
def bufferedModelTargets (A : BufferedAtlas M E) (c : E ≃L[ℝ] (Fin d → ℝ)) :=
  modelCoordinateDomains c (fun i => (A.chart i).target)

/-- Original inner evaluation domains expressed in component coordinates. -/
def bufferedModelInner (A : BufferedAtlas M E) (c : E ≃L[ℝ] (Fin d → ℝ)) :=
  modelCoordinateDomains c (bufferedInnerCoordinates A)

/-- The same fixed genuine sampling buffers expressed in component coordinates. -/
def bufferedModelSampling (A : BufferedAtlas M E) (c : E ≃L[ℝ] (Fin d → ℝ)) :=
  modelCoordinateDomains c (bufferedSamplingCoordinates A)

theorem bufferedModelTargets_open (A : BufferedAtlas M E) (c : E ≃L[ℝ] (Fin d → ℝ))
    (i : Fin A.count) : IsOpen (bufferedModelTargets A c i) :=
  modelCoordinateDomains_open c (fun i => (A.chart i).open_target) i

theorem bufferedModelSampling_subset_target (A : BufferedAtlas M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (i : Fin A.count) :
    bufferedModelSampling A c i ⊆ bufferedModelTargets A c i :=
  fun _ hx => bufferedSampling_subset_target A i hx

theorem bufferedModelInner_subset_target (A : BufferedAtlas M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (i : Fin A.count) :
    bufferedModelInner A c i ⊆ bufferedModelTargets A c i := fun _ hx => hx.1

variable [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Genuine source smoothness in the original atlas model. -/
theorem bufferedNativeCoordinates_contDiffOn (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) {u : M → Fin q → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin q → ℝ) ∞ u) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (bufferedNativeCoordinates A u i) (A.chart i).target :=
  (hu.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i))).contDiffOn

/-- The same source is smooth in the actual component-coordinate presentation. -/
theorem bufferedModelCoordinates_contDiffOn (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (c : E ≃L[ℝ] (Fin d → ℝ)) {u : M → Fin q → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin q → ℝ) ∞ u) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (bufferedModelCoordinates A c u i) (bufferedModelTargets A c i) :=
  modelCoordinateFamily_contDiffOn c (bufferedNativeCoordinates_contDiffOn A hA hu) i

end

end GlobalEmbedding.Offline
