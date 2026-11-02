import GlobalEmbedding.Offline.BufferedWeightedSmoothing

/-!
# Fixed-Lebesgue-kernel global map consumer

Source: `main.tex` 700–720, equation (6.4), actual buffered localization.
The normalized bump and signed kernel are constructed, the charts/cutoffs are
the original reference-data providers, and the result is ONE globally smooth
map on the original manifold. The exact original base-two weighted norm is
used with the error in its original `u - S_ell u` orientation.

All model coordinates here are spatial. No parameter-product total C2 norm
is substituted for spatial-twojet plus total derivatives; tensor bundle-frame
gluing is likewise a separate obligation.
-/

open MeasureTheory GlobalEmbedding.Paper Function Set Manifold
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Offline

noncomputable section

variable {d q : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℝ) M] [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

/-- Reversing the actual global error preserves its original weighted atlas
norm, by the original coordinate-partial identity, not by changing the norm. -/
theorem paperAtlasWeighted_buffered_sub_comm (A : BufferedAtlas M (Fin d → ℝ))
    (hA : IsSmoothBufferedAtlas A) (base m : ℕ) (tau : ℝ) (u v : M → Fin q → ℝ)
    (hu : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin q → ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin q → ℝ) ∞ v) :
    paperAtlasWeighted base m tau (bufferedAtlasCoordinates A (u - v))
      (fun i => (A.chart i).target) (bufferedInnerCoordinates A) =
    paperAtlasWeighted base m tau (bufferedAtlasCoordinates A (v - u))
      (fun i => (A.chart i).target) (bufferedInnerCoordinates A) := by
  exact paperAtlasWeighted_sub_comm base m tau (bufferedAtlasCoordinates A u) (bufferedAtlasCoordinates A v)
    (fun i => (A.chart i).target) (bufferedInnerCoordinates A) (fun i => (A.chart i).open_target)
    (fun _ _ hy => hy.1) (bufferedAtlasCoordinates_contDiffOn A hA hu) (bufferedAtlasCoordinates_contDiffOn A hA hv)

/-- The full actual global MAP tail estimate in original base-two norm, for
the constructed signed Lebesgue kernel and every `0 < tau ≤ ell ≤ t ≤ 1`.
The conclusion contains both genuine global smoothness and guarded original
weighted-norm approximation. The constant has no atlas or chart-count argument. -/
theorem fixedKernel_buffered_map_smoothing_tail (A : BufferedAtlas M (Fin d → ℝ))
    (hA : IsSmoothBufferedAtlas A) (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ A.buffer)
    (m r : ℕ) {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : M → Fin q → ℝ} (hu : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin q → ℝ) ∞ u)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hNr : paperAtlasWeighted 2 r t (bufferedAtlasCoordinates A u)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A) ≠ ⊤)
    (hNm : paperAtlasWeighted 2 m t (bufferedAtlasCoordinates A u)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A) ≠ ⊤)
    (budget : ℝ) (hbudget : (paperAtlasWeighted 2 r t (bufferedAtlasCoordinates A u)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A)).toReal ≤ budget) :
    let K := fixedSmoothingKernel (volume : Measure (Fin d → ℝ)) rho hrho r
    let kappa := normalizedSmoothingBase (volume : Measure (Fin d → ℝ)) rho hrho
    let S := bufferedSmoothing A volume K ell chi u
    let e := bufferedAtlasCoordinates A (u - S)
    let O := fun i => (A.chart i).target
    ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin q → ℝ) ∞ S ∧
      paperAtlasWeighted 2 m tau e O (bufferedInnerCoordinates A) ≠ ⊤ ∧
      (paperAtlasWeighted 2 m tau e O (bufferedInnerCoordinates A)).toReal ≤
        paperBufferedSmoothingTailConstant volume kappa B T D 2 m r *
          (budget * (ell / t) ^ r + (paperAtlasWeighted 2 m t (bufferedAtlasCoordinates A u)
            O (bufferedSamplingCoordinates A)).toReal * (tau / t) ^ r) := by
  dsimp only
  let K := fixedSmoothingKernel (volume : Measure (Fin d → ℝ)) rho hrho r
  have hb := normalizedSmoothingBase_spec (volume : Measure (Fin d → ℝ)) rho hrho
  have hK := fixedSmoothingKernel_spec (volume : Measure (Fin d → ℝ)) rho hrho r
  have hS := bufferedSmoothing_contMDiff A hA volume hK.1 hK.2.1 hK.2.2.1 hbuffer
    (htau.trans_le htaul).le (helt.trans ht1) chi hchi hchiSupport hu
  refine ⟨hS, ?_⟩
  rw [paperAtlasWeighted_buffered_sub_comm A hA 2 m tau u _ hu hS]
  exact paperAtlasWeighted_buffered_smoothing_tail A hA volume hb.1 hb.2.1 hb.2.2.1 2 m r
    hK.2.2.1 hbuffer htau htaul helt ht1 chi hchi hchiSupport hpartition hu
    B T hB hT D hD hweight htransition hNr hNm budget hbudget

end

end GlobalEmbedding.Offline
