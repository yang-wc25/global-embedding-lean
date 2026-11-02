import GlobalEmbedding.Offline.BufferedModelWeighted
import GlobalEmbedding.Offline.BufferedEuclideanSmoothing

/-!
# The actual global smoother on the original Euclidean source and target

Source: `main.tex` 234 and 700–720, equation (6.4), and the original source
coordinate convention in `IncrementsOriginalNativeCoordinates.lean`.
The original Euclidean buffered atlas, its actual balls and buffers, and the
genuine Euclidean target are retained. Component coordinates use the actual
`WithLp.toLp 2` map; both source-model operator-norm costs are explicit.
The conclusion concerns the SAME global smooth map assembled from the actual
signed Lebesgue integrals and original square partition. This is the spatial,
unparameterized map estimate. Tensor frames and spatial/parameter jet packets
remain distinct obligations.
-/

open MeasureTheory GlobalEmbedding.Paper Function Set Manifold
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Offline

noncomputable section

section Symmetry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {d q : ℕ}

/-- Reversing the actual global error in the original component norm, while
retaining the original source model and the same atlas. -/
theorem paperAtlasWeighted_model_buffered_sub_comm (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (c : E ≃L[ℝ] (Fin d → ℝ))
    (base m : ℕ) (tau : ℝ) (u v : M → Fin q → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin q → ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin q → ℝ) ∞ v) :
    paperAtlasWeighted base m tau (bufferedModelCoordinates A c (u - v))
      (bufferedModelTargets A c) (bufferedModelInner A c) =
    paperAtlasWeighted base m tau (bufferedModelCoordinates A c (v - u))
      (bufferedModelTargets A c) (bufferedModelInner A c) := by
  exact paperAtlasWeighted_sub_comm base m tau
    (bufferedModelCoordinates A c u) (bufferedModelCoordinates A c v)
    (bufferedModelTargets A c) (bufferedModelInner A c)
    (bufferedModelTargets_open A c) (bufferedModelInner_subset_target A c)
    (bufferedModelCoordinates_contDiffOn A hA c hu) (bufferedModelCoordinates_contDiffOn A hA c hv)

end Symmetry

variable {d q : ℕ} {M : Type*} [TopologicalSpace M]

/-- Literal component representatives in the ORIGINAL Euclidean source atlas. -/
def bufferedOriginalEuclideanCoordinates (A : BufferedAtlas M (EuclideanSpace ℝ (Fin d)))
    (u : M → EuclideanSpace ℝ (Fin q)) :=
  bufferedModelCoordinates A (EuclideanSpace.equiv (Fin d) ℝ) (EuclideanSpace.equiv (Fin q) ℝ ∘ u)

/-- The source argument is literally the original Euclidean `toLp 2` point,
and the target value is literally the component of the same original map. -/
theorem bufferedOriginalEuclideanCoordinates_apply (A : BufferedAtlas M (EuclideanSpace ℝ (Fin d)))
    (u : M → EuclideanSpace ℝ (Fin q)) (i : Fin A.count) (x : Fin d → ℝ) (j : Fin q) :
    bufferedOriginalEuclideanCoordinates A u i x j =
      u ((A.chart i).symm (WithLp.toLp 2 x)) j := rfl

/-- Actual original differentiation domains, expressed in component coordinates. -/
def bufferedOriginalEuclideanTargets (A : BufferedAtlas M (EuclideanSpace ℝ (Fin d))) :=
  bufferedModelTargets A (EuclideanSpace.equiv (Fin d) ℝ)

/-- Actual original inner evaluation domains, expressed in component coordinates. -/
def bufferedOriginalEuclideanInner (A : BufferedAtlas M (EuclideanSpace ℝ (Fin d))) :=
  bufferedModelInner A (EuclideanSpace.equiv (Fin d) ℝ)

/-- Fixed genuine original sampling buffers, expressed in component coordinates. -/
def bufferedOriginalEuclideanSampling (A : BufferedAtlas M (EuclideanSpace ℝ (Fin d))) :=
  bufferedModelSampling A (EuclideanSpace.equiv (Fin d) ℝ)

variable [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]

/-- Global map equation (6.4) on the original Euclidean source AND target.
The actual finite signed-kernel smoothing is globally smooth; its original
base-two coordinate norm is finite and satisfies the two-term tail estimate.
The displayed constant is explicit before the atlas and has no chart count.
Only order-r moments are used for the C^(r+2) source input. -/
theorem fixedKernel_original_euclidean_map_smoothing_tail
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ A.buffer) (m r : ℕ)
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i) (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : M → EuclideanSpace ℝ (Fin q)}
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ u)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hNr : paperAtlasWeighted 2 r t (bufferedOriginalEuclideanCoordinates A u)
      (bufferedOriginalEuclideanTargets A) (bufferedOriginalEuclideanSampling A) ≠ ⊤)
    (hNm : paperAtlasWeighted 2 m t (bufferedOriginalEuclideanCoordinates A u)
      (bufferedOriginalEuclideanTargets A) (bufferedOriginalEuclideanSampling A) ≠ ⊤)
    (budget : ℝ) (hbudget : (paperAtlasWeighted 2 r t (bufferedOriginalEuclideanCoordinates A u)
      (bufferedOriginalEuclideanTargets A) (bufferedOriginalEuclideanSampling A)).toReal ≤ budget) :
    let c := EuclideanSpace.equiv (Fin d) ℝ
    let K := fixedSmoothingKernel (volume : Measure (EuclideanSpace ℝ (Fin d))) rho hrho r
    let kappa := normalizedSmoothingBase (volume : Measure (EuclideanSpace ℝ (Fin d))) rho hrho
    let S := bufferedSmoothing A volume K ell chi u
    let e := bufferedOriginalEuclideanCoordinates A (u - S)
    let O := bufferedOriginalEuclideanTargets A
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ S ∧
      paperAtlasWeighted 2 m tau e O (bufferedOriginalEuclideanInner A) ≠ ⊤ ∧
      (paperAtlasWeighted 2 m tau e O (bufferedOriginalEuclideanInner A)).toReal ≤
        modelBufferedSmoothingTailConstant c volume kappa B T D 2 m r *
          (budget * (ell / t) ^ r + (paperAtlasWeighted 2 m t (bufferedOriginalEuclideanCoordinates A u)
            O (bufferedOriginalEuclideanSampling A)).toReal * (tau / t) ^ r) := by
  dsimp only
  let c := EuclideanSpace.equiv (Fin d) ℝ
  let e := EuclideanSpace.equiv (Fin q) ℝ
  let K := fixedSmoothingKernel (volume : Measure (EuclideanSpace ℝ (Fin d))) rho hrho r
  have huPi : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, Fin q → ℝ) ∞ (e ∘ u) :=
    e.contDiff.contMDiff.comp hu
  have hb := normalizedSmoothingBase_spec (volume : Measure (EuclideanSpace ℝ (Fin d))) rho hrho
  have hK := fixedSmoothingKernel_spec (volume : Measure (EuclideanSpace ℝ (Fin d))) rho hrho r
  have hS := bufferedSmoothing_contMDiff A hA volume hK.1 hK.2.1 hK.2.2.1 hbuffer
    (htau.trans_le htaul).le (helt.trans ht1) chi hchi hchiSupport hu
  have hSPi := bufferedSmoothing_contMDiff A hA volume hK.1 hK.2.1 hK.2.2.1 hbuffer
    (htau.trans_le htaul).le (helt.trans ht1) chi hchi hchiSupport huPi
  have h := paperAtlasWeighted_model_buffered_smoothing_tail A c hA volume hb.1 hb.2.1 hb.2.2.1
    2 m r hK.2.2.1 hbuffer htau htaul helt ht1 chi hchi hchiSupport hpartition huPi
    B T hB hT D hD hweight htransition hNr hNm budget hbudget
  dsimp only at h
  have hcomm := paperAtlasWeighted_model_buffered_sub_comm A hA c 2 m tau
    (e ∘ u) (bufferedSmoothing A volume K ell chi (e ∘ u)) huPi hSPi
  simp only [K, fixedSmoothingKernel] at hcomm
  rw [← hcomm] at h
  have hnatural := bufferedSmoothing_equiv A volume K ell chi e u
  have herror : bufferedModelCoordinates A c ((e ∘ u) - bufferedSmoothing A volume K ell chi (e ∘ u)) =
      bufferedOriginalEuclideanCoordinates A (u - bufferedSmoothing A volume K ell chi u) := by
    rw [hnatural]
    funext i z
    exact (e.map_sub _ _).symm
  refine ⟨hS, ?_⟩
  rw [← herror]
  exact h

end

end GlobalEmbedding.Offline
