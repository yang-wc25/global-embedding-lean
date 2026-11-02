import GlobalEmbedding.Paper.BufferedAtlas
import GlobalEmbedding.Offline.FixedSmoothingKernel
import GlobalEmbedding.Offline.LocalSmoothingEstimates
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# One actual smoothing map on the original buffered manifold atlas

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 700–720,
and the original node `repair-buffered-smoothing-localization`.

The charts, inner domains and common buffer are the original `BufferedAtlas`.
Coordinate sources are literally extended by zero outside the actual chart
target. Each local convolution is pulled back through the actual chart and
extended by zero outside its source. A finite square partition then defines
one global map. Smoothness is proved on its actual support germs; no global
smoothness of a coordinate zero extension or compactness of the source is
assumed. Every sampled point used at an active cutoff lies inside its chart.

This module constructs maps with a fixed vector target. Tensor frame changes
and parameter-spatial jet assembly are separate obligations.
-/

open MeasureTheory GlobalEmbedding.Paper Function Filter Set Manifold IsManifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Offline

noncomputable section

variable {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M]

/-- The genuine open coordinate image of the original inner chart domain. -/
def bufferedInnerCoordinates (A : BufferedAtlas M E) (i : Fin A.count) : Set E :=
  (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.inner i

/-- The source field in a real chart, literally zero off that chart target. -/
def bufferedCoordinateExtension (A : BufferedAtlas M E) (u : M → F)
    (i : Fin A.count) : E → F :=
  (A.chart i).target.indicator (u ∘ (A.chart i).symm)

variable [MeasurableSpace E]

/-- The actual local convolution of the original zero-extended coordinate field. -/
def bufferedLocalSmoothing (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (u : M → F) (i : Fin A.count) : E → F :=
  signedSmoothing mu K ell (bufferedCoordinateExtension A u i)

/-- Pull the actual local convolution back and set it zero off the chart source. -/
def bufferedChartSmoothing (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (u : M → F) (i : Fin A.count) : M → F :=
  (A.chart i).source.indicator (bufferedLocalSmoothing A mu K ell u i ∘ A.chart i)

/-- The i-th actual localized map, with the square of the original cutoff. -/
def bufferedSmoothingTerm (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ) (u : M → F)
    (i : Fin A.count) : M → F :=
  fun x => chi i x ^ 2 • bufferedChartSmoothing A mu K ell u i x

/-- One global map, built from the actual charts and actual integral values. -/
def bufferedSmoothing (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ) (u : M → F) : M → F :=
  fun x => ∑ i, bufferedSmoothingTerm A mu K ell chi u i x

omit [MeasurableSpace E] [NormedSpace ℝ E] in
/-- Original inner domains have genuine open coordinate images. -/
theorem bufferedInnerCoordinates_open (A : BufferedAtlas M E) (i : Fin A.count) :
    IsOpen (bufferedInnerCoordinates A i) :=
  (A.chart i).isOpen_inter_preimage_symm (A.inner_open i)

omit [MeasurableSpace E] [NormedSpace ℝ E] in
/-- An inner point has the expected actual coordinate and inverse identities. -/
theorem bufferedInnerCoordinates_mem (A : BufferedAtlas M E) (i : Fin A.count)
    {x : M} (hx : x ∈ A.inner i) : A.chart i x ∈ bufferedInnerCoordinates A i := by
  refine ⟨(A.chart i).map_source (A.inner_subset i hx), ?_⟩
  change (A.chart i).symm (A.chart i x) ∈ A.inner i
  simpa only [(A.chart i).left_inv (A.inner_subset i hx)] using hx

omit [MeasurableSpace E] in
/-- The same common buffer contains every actual kernel segment for every
scale in `[0,1]`. No minimum over charts or extra small-scale threshold occurs. -/
theorem buffered_kernel_segment (A : BufferedAtlas M E) (i : Fin A.count)
    {K : E → ℝ} {rho ell : ℝ} (hK : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    {z : E} (hz : z ∈ bufferedInnerCoordinates A i)
    {y : E} (hy : y ∈ tsupport K) {s : ℝ} (hs : s ∈ Icc 0 1) :
    z - s • (ell • y) ∈ (A.chart i).target := by
  apply A.buffered i ((A.chart i).symm z) hz.2
  change dist (z - s • (ell • y)) (A.chart i ((A.chart i).symm z)) < A.buffer
  rw [(A.chart i).right_inv hz.1, dist_eq_norm, sub_sub_cancel_left, norm_neg]
  have hy' : ‖y‖ < rho := by simpa only [Metric.mem_ball, dist_zero_right] using hK hy
  have hle : ‖s • (ell • y)‖ ≤ ‖y‖ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hs.1, abs_of_nonneg hell]
    calc
      s * (ell * ‖y‖) ≤ 1 * (ell * ‖y‖) :=
        mul_le_mul_of_nonneg_right hs.2 (mul_nonneg hell (norm_nonneg y))
      _ ≤ ‖y‖ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hell1 (norm_nonneg y)
  exact hle.trans_lt (hy'.trans_le hrho)

omit [MeasurableSpace E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- On its open target, the zero extension has the original coordinate germ. -/
theorem bufferedCoordinateExtension_eventuallyEq (A : BufferedAtlas M E) (u : M → F)
    (i : Fin A.count) {z : E} (hz : z ∈ (A.chart i).target) :
    bufferedCoordinateExtension A u i =ᶠ[𝓝 z] (u ∘ (A.chart i).symm) := by
  filter_upwards [(A.chart i).open_target.mem_nhds hz] with y hy
  exact Set.indicator_of_mem hy _

omit [MeasurableSpace E] in
/-- Every actual coordinate jet is unchanged by zero extension at target points. -/
theorem iteratedFDeriv_bufferedCoordinateExtension (A : BufferedAtlas M E) (u : M → F)
    (i : Fin A.count) (j : ℕ) {z : E} (hz : z ∈ (A.chart i).target) :
    iteratedFDeriv ℝ j (bufferedCoordinateExtension A u i) z =
      iteratedFDeriv ℝ j (u ∘ (A.chart i).symm) z :=
  ((bufferedCoordinateExtension_eventuallyEq A u i hz).iteratedFDeriv ℝ j).eq_of_nhds

variable [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- Source regularity in the actual target; no boundary regularity of the
zero extension is asserted or used. -/
theorem bufferedCoordinateExtension_contDiffOn (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) {u : M → F}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (bufferedCoordinateExtension A u i) (A.chart i).target := by
  have hc : ContDiffOn ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i).target :=
    (hu.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i))).contDiffOn
  intro z hz
  exact ((hc.contDiffAt ((A.chart i).open_target.mem_nhds hz)).congr_of_eventuallyEq
    (bufferedCoordinateExtension_eventuallyEq A u i hz)).contDiffWithinAt

omit [CompleteSpace F] in
/-- The actual local smoothing is smooth on the original inner-coordinate domain. -/
theorem bufferedLocalSmoothing_contDiffOn (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    {u : M → F} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (bufferedLocalSmoothing A mu K ell u i) (bufferedInnerCoordinates A i) := by
  apply signedSmoothing_contDiffOn mu hK hcompact (bufferedInnerCoordinates_open A i)
    (A.chart i).open_target (bufferedCoordinateExtension_contDiffOn A hA hu i) ell
  intro z hz y hy
  simpa only [one_smul] using buffered_kernel_segment A i hsupp hrho hell hell1 hz hy
    (s := 1) (by simp)

omit [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Localization has the actual original cutoff support, including at chart boundaries. -/
theorem bufferedSmoothingTerm_tsupport_subset (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ) (u : M → F)
    (i : Fin A.count) : tsupport (bufferedSmoothingTerm A mu K ell chi u i) ⊆ tsupport (chi i) := by
  apply (tsupport_smul_subset_left (fun x => chi i x ^ 2) _).trans
  simpa only [pow_two] using (tsupport_mul_subset_left (f := chi i) (g := chi i))

omit [CompleteSpace F] in
/-- Each literal chart pullback extended by zero is globally smooth after
the original cutoff. The proof uses its true support and an actual local chart germ. -/
theorem bufferedSmoothingTerm_contMDiff (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    {u : M → F} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u) (i : Fin A.count) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (bufferedSmoothingTerm A mu K ell chi u i) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hi : x ∈ A.inner i := hchiSupport i (bufferedSmoothingTerm_tsupport_subset A mu K ell chi u i hx)
  have hxSource := A.inner_subset i hi
  have hs := bufferedLocalSmoothing_contDiffOn A hA mu hK hcompact hsupp hrho hell hell1 hu i
  have hsat := (hs.contDiffAt ((bufferedInnerCoordinates_open A i).mem_nhds
    (bufferedInnerCoordinates_mem A i hi))).contMDiffAt
  have hc := hsat.comp x (contMDiffAt_of_mem_maximalAtlas (hA.chart_mem i) hxSource)
  have hzero : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (bufferedChartSmoothing A mu K ell u i) x := by
    apply hc.congr_of_eventuallyEq
    filter_upwards [(A.chart i).open_source.mem_nhds hxSource] with z hz
    exact Set.indicator_of_mem hz _
  change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞
    (fun y => chi i y ^ 2 • bufferedChartSmoothing A mu K ell u i y) x
  simp only [pow_two]
  exact (((hchi i).contMDiffAt).mul ((hchi i).contMDiffAt)).smul hzero

omit [CompleteSpace F] in
/-- The same finite-sum operator is globally manifold-smooth. No local values
are assumed compatible; the actual square partition performs the gluing. -/
theorem bufferedSmoothing_contMDiff (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    {u : M → F} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (bufferedSmoothing A mu K ell chi u) := by
  exact ContMDiff.sum fun i _ => bufferedSmoothingTerm_contMDiff A hA mu hK hcompact
    hsupp hrho hell hell1 chi hchi hchiSupport hu i

omit [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Exact error decomposition for the SAME global map. The original partition
identity and genuine chart inverse laws remove every unsmoothed input term. -/
theorem bufferedSmoothing_error_eq (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1) (u : M → F) (x : M) :
    bufferedSmoothing A mu K ell chi u x - u x =
      ∑ i, chi i x ^ 2 • (bufferedLocalSmoothing A mu K ell u i (A.chart i x) -
        bufferedCoordinateExtension A u i (A.chart i x)) := by
  have hsingle (i : Fin A.count) :
      bufferedSmoothingTerm A mu K ell chi u i x - chi i x ^ 2 • u x =
        chi i x ^ 2 • (bufferedLocalSmoothing A mu K ell u i (A.chart i x) -
          bufferedCoordinateExtension A u i (A.chart i x)) := by
    by_cases hi : chi i x = 0
    · simp only [bufferedSmoothingTerm, hi, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        zero_smul, sub_zero]
    · have hx := A.inner_subset i (hchiSupport i (subset_tsupport (chi i) hi))
      rw [bufferedSmoothingTerm, bufferedChartSmoothing, Set.indicator_of_mem hx,
        Function.comp_apply, bufferedCoordinateExtension,
        Set.indicator_of_mem ((A.chart i).map_source hx), Function.comp_apply,
        (A.chart i).left_inv hx]
      exact (smul_sub _ _ _).symm
  have hsum : (∑ i, chi i x ^ 2 • u x) = u x := by
    rw [← Finset.sum_smul, hpartition x, one_smul]
  change (∑ i, bufferedSmoothingTerm A mu K ell chi u i x) - u x = _
  conv_lhs => rw [← hsum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => hsingle i)

omit [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Convexity of the genuine square partition transfers active local errors
to the actual global error with NO chart-count or overlap factor at order zero. -/
theorem norm_bufferedSmoothing_error_le (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1) (u : M → F) (x : M) (B : ℝ)
    (hlocal : ∀ i, x ∈ tsupport (chi i) →
      ‖bufferedLocalSmoothing A mu K ell u i (A.chart i x) -
        bufferedCoordinateExtension A u i (A.chart i x)‖ ≤ B) :
    ‖bufferedSmoothing A mu K ell chi u x - u x‖ ≤ B := by
  rw [bufferedSmoothing_error_eq A mu K ell chi hchiSupport hpartition u x]
  calc
    ‖∑ i, chi i x ^ 2 • (bufferedLocalSmoothing A mu K ell u i (A.chart i x) -
        bufferedCoordinateExtension A u i (A.chart i x))‖ ≤
        ∑ i, ‖chi i x ^ 2 • (bufferedLocalSmoothing A mu K ell u i (A.chart i x) -
          bufferedCoordinateExtension A u i (A.chart i x))‖ := norm_sum_le _ _
    _ ≤ ∑ i, chi i x ^ 2 * B := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : chi i x = 0
      · simp only [hi, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_smul, norm_zero,
          zero_mul, le_refl]
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hlocal i (subset_tsupport (chi i) hi)) (sq_nonneg _)
    _ = B := by rw [← Finset.sum_mul, hpartition x, one_mul]

/-- Actual global order-r C0 approximation from original chart derivative
bounds. All constants come from the same constructed signed kernel, and the
only input estimates are source jets on the actual chart targets. -/
theorem bufferedSmoothing_error_le_of_jet_bound (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {kappa : E → ℝ} (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (hmass : (∫ y, kappa y ∂mu) = 1) (r : ℕ)
    {rho ell : ℝ} (hsupp : tsupport (finiteMomentKernel r kappa) ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : M → F} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ i k, k ≤ r → ∀ z ∈ (A.chart i).target,
      ‖iteratedFDeriv ℝ k (u ∘ (A.chart i).symm) z‖ ≤ B) (x : M) :
    ‖bufferedSmoothing A mu (finiteMomentKernel r kappa) ell chi u x - u x‖ ≤
      kernelTailConstant mu (finiteMomentKernel r kappa) r * B * ell ^ r := by
  apply norm_bufferedSmoothing_error_le A mu _ ell chi hchiSupport hpartition u x
  intro i hi
  have hx := bufferedInnerCoordinates_mem A i (hchiSupport i hi)
  have htail := signedSmoothing_low_derivative_error_le mu hsmooth hcompact hmass r
    (bufferedInnerCoordinates_open A i) (A.chart i).open_target (fun _ hz => hz.1)
    (bufferedCoordinateExtension_contDiffOn A hA hu i) hell
    (fun z hz y hy s hs => buffered_kernel_segment A i hsupp hrho hell hell1 hz hy hs)
    B hB0 (by
      intro k hk z hz
      rw [iteratedFDeriv_bufferedCoordinateExtension A u i k hz]
      exact hB i k hk z hz) (j := 0) (Nat.zero_le r) hx
  change ‖signedSmoothing mu (finiteMomentKernel r kappa) ell
    (bufferedCoordinateExtension A u i) (A.chart i x) -
    bufferedCoordinateExtension A u i (A.chart i x)‖ ≤ _
  simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using htail

end

end GlobalEmbedding.Offline
