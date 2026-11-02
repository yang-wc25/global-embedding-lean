import GlobalEmbedding.Offline.BufferedSmoothing

/-!
# Linearity of the same actual buffered manifold smoothing

Source: `main.tex` 700–720 and `repair-buffered-smoothing-localization`.
Only the kernel samples at active cutoffs are used. Their integrability is
proved from source smoothness on the actual target and compact kernel support;
no global integrability of a raw zero extension is required. The resulting
linear map acts on genuine native smooth maps on the original manifold.
-/

open MeasureTheory GlobalEmbedding.Paper Function Set Manifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Offline

noncomputable section

variable {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- True integrability at every output point where the original common buffer applies. -/
theorem bufferedLocalSmoothing_integrable (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    {u : M → F} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u)
    (i : Fin A.count) {z : E} (hz : z ∈ bufferedInnerCoordinates A i) :
    Integrable (fun y => K y • bufferedCoordinateExtension A u i (z - ell • y)) mu := by
  have hcont : ContinuousOn (fun y => bufferedCoordinateExtension A u i (z - ell • y))
      (tsupport K) := by
    apply (bufferedCoordinateExtension_contDiffOn A hA hu i).continuousOn.comp
      (continuous_const.sub (continuous_const.smul continuous_id)).continuousOn
    intro y hy
    change z - ell • y ∈ (A.chart i).target
    simpa only [one_smul] using buffered_kernel_segment A i hsupp hrho hell hell1 hz hy
      (s := 1) (by simp)
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_smul_subset_left _ _).trans (subset_tsupport K))).mp
    ((hK.continuous.continuousOn.smul hcont).integrableOn_compact hcompact)

/-- Additivity of the literal global integral construction on smooth inputs. -/
theorem bufferedSmoothing_add (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ) (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    {u v : M → F} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ v) :
    bufferedSmoothing A mu K ell chi (u + v) =
      bufferedSmoothing A mu K ell chi u + bufferedSmoothing A mu K ell chi v := by
  funext x
  change (∑ i, bufferedSmoothingTerm A mu K ell chi (u + v) i x) =
    (∑ i, bufferedSmoothingTerm A mu K ell chi u i x) +
      (∑ i, bufferedSmoothingTerm A mu K ell chi v i x)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : chi i x = 0
  · simp only [bufferedSmoothingTerm, hi, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_smul, add_zero]
  · have hxInner := hchiSupport i (subset_tsupport (chi i) hi)
    have hxSource := A.inner_subset i hxInner
    have hz := bufferedInnerCoordinates_mem A i hxInner
    have hIu := bufferedLocalSmoothing_integrable A hA mu hK hcompact hsupp hrho hell hell1 hu i hz
    have hIv := bufferedLocalSmoothing_integrable A hA mu hK hcompact hsupp hrho hell hell1 hv i hz
    have hext : bufferedCoordinateExtension A (u + v) i =
        bufferedCoordinateExtension A u i + bufferedCoordinateExtension A v i := by
      funext y
      by_cases hy : y ∈ (A.chart i).target
      · simp only [bufferedCoordinateExtension, Set.indicator_of_mem hy,
          Function.comp_apply, Pi.add_apply]
      · simp only [bufferedCoordinateExtension, Set.indicator_of_notMem hy,
          Pi.add_apply, add_zero]
    have hlocal : bufferedLocalSmoothing A mu K ell (u + v) i (A.chart i x) =
        bufferedLocalSmoothing A mu K ell u i (A.chart i x) +
          bufferedLocalSmoothing A mu K ell v i (A.chart i x) := by
      change (∫ y, K y • bufferedCoordinateExtension A (u + v) i (A.chart i x - ell • y) ∂mu) = _
      rw [hext]
      simp only [Pi.add_apply, smul_add]
      exact integral_add hIu hIv
    simp only [bufferedSmoothingTerm, bufferedChartSmoothing, Set.indicator_of_mem hxSource,
      Function.comp_apply, hlocal, smul_add]

omit [CompleteSpace F] [BorelSpace E] [FiniteDimensional ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Homogeneity of the literal construction; the real scalar commutes with
the Bochner integral and with the actual indicator extensions. -/
theorem bufferedSmoothing_smul (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ) (u : M → F) (c : ℝ) :
    bufferedSmoothing A mu K ell chi (c • u) = c • bufferedSmoothing A mu K ell chi u := by
  have hext (i : Fin A.count) : bufferedCoordinateExtension A (c • u) i =
      c • bufferedCoordinateExtension A u i := by
    funext y
    by_cases hy : y ∈ (A.chart i).target
    · simp only [bufferedCoordinateExtension, Set.indicator_of_mem hy,
        Function.comp_apply, Pi.smul_apply]
    · simp only [bufferedCoordinateExtension, Set.indicator_of_notMem hy,
        Pi.smul_apply, smul_zero]
  have hlocal (i : Fin A.count) (z : E) : bufferedLocalSmoothing A mu K ell (c • u) i z =
      c • bufferedLocalSmoothing A mu K ell u i z := by
    change (∫ y, K y • bufferedCoordinateExtension A (c • u) i (z - ell • y) ∂mu) = _
    rw [hext]
    simp only [Pi.smul_apply, smul_comm (K _) c]
    exact integral_smul c _
  funext x
  change (∑ i, bufferedSmoothingTerm A mu K ell chi (c • u) i x) =
    c • ∑ i, bufferedSmoothingTerm A mu K ell chi u i x
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ (A.chart i).source
  · simp only [bufferedSmoothingTerm, bufferedChartSmoothing, Set.indicator_of_mem hx,
      Function.comp_apply, hlocal, smul_comm (chi i x ^ 2) c]
  · simp only [bufferedSmoothingTerm, bufferedChartSmoothing, Set.indicator_of_notMem hx, smul_zero]

/-- The native linear operator on genuine smooth maps whose underlying function
is exactly the preceding global buffered smoothing, with the same fixed charts
and cutoff data. No output field or smoothness premise is supplied by the caller. -/
def bufferedSmoothingLinearMap (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i) :
    C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), F⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), F⟯ where
  toFun u := ⟨bufferedSmoothing A mu K ell chi u,
    bufferedSmoothing_contMDiff A hA mu hK hcompact hsupp hrho hell hell1 chi hchi hchiSupport u.contMDiff⟩
  map_add' u v := by
    apply ContMDiffMap.coe_injective
    exact bufferedSmoothing_add A hA mu hK hcompact hsupp hrho hell hell1 chi hchiSupport
      u.contMDiff v.contMDiff
  map_smul' c u := by
    apply ContMDiffMap.coe_injective
    exact bufferedSmoothing_smul A mu K ell chi u c

end

end GlobalEmbedding.Offline
