import GlobalEmbedding.Offline.BufferedSmoothing

/-!
# Fixed original sampling buffers for every smoothing scale

Source: `main.tex` 700–720 and `repair-buffered-smoothing-localization`.
The source norm is evaluated on the union of the ORIGINAL common-buffer balls
around the original inner coordinates. This open set is contained in the
actual chart target and contains all kernel segments for every ell in [0,1].
It does not depend on ell. Quantitative source bounds are thus needed on this
actual sampling buffer, not on the whole chart target and not just the inner
domain. Differentiation may still take place on the original chart target.
-/

open GlobalEmbedding.Paper MeasureTheory Set Metric
open scoped ContDiff

namespace GlobalEmbedding.Offline

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]

/-- The fixed genuine buffer sampled by all admissible scales. -/
def bufferedSamplingCoordinates (A : BufferedAtlas M E) (i : Fin A.count) : Set E :=
  ⋃ z ∈ bufferedInnerCoordinates A i, Metric.ball z A.buffer

omit [NormedSpace ℝ E] in
/-- The sampling buffer is open, without any compactness assumption. -/
theorem bufferedSamplingCoordinates_open (A : BufferedAtlas M E) (i : Fin A.count) :
    IsOpen (bufferedSamplingCoordinates A i) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

omit [NormedSpace ℝ E] in
/-- The original inner coordinates lie in the fixed sampling buffer. -/
theorem bufferedInner_subset_sampling (A : BufferedAtlas M E) (i : Fin A.count) :
    bufferedInnerCoordinates A i ⊆ bufferedSamplingCoordinates A i := by
  intro z hz
  exact mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, by simpa only [mem_ball, dist_self] using A.buffer_pos⟩⟩

omit [NormedSpace ℝ E] in
/-- The entire fixed sampling buffer lies inside the ORIGINAL chart target. -/
theorem bufferedSampling_subset_target (A : BufferedAtlas M E) (i : Fin A.count) :
    bufferedSamplingCoordinates A i ⊆ (A.chart i).target := by
  intro y hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp hy
  obtain ⟨hzInner, hyball⟩ := mem_iUnion.mp hz
  apply A.buffered i ((A.chart i).symm z) hzInner.2
  simpa only [(A.chart i).right_inv hzInner.1] using hyball

/-- Every actual convolution/Taylor segment lies in that same scale-independent
sampling buffer, derived from its definition and the original common radius. -/
theorem buffered_kernel_segment_mem_sampling (A : BufferedAtlas M E) (i : Fin A.count)
    {K : E → ℝ} {rho ell : ℝ} (hK : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    {z : E} (hz : z ∈ bufferedInnerCoordinates A i)
    {y : E} (hy : y ∈ tsupport K) {s : ℝ} (hs : s ∈ Icc 0 1) :
    z - s • (ell • y) ∈ bufferedSamplingCoordinates A i := by
  apply mem_iUnion.mpr
  refine ⟨z, mem_iUnion.mpr ⟨hz, ?_⟩⟩
  change dist (z - s • (ell • y)) z < A.buffer
  rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
  have hy' : ‖y‖ < rho := by simpa only [mem_ball, dist_zero_right] using hK hy
  have hle : ‖s • (ell • y)‖ ≤ ‖y‖ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hs.1, abs_of_nonneg hell]
    calc
      s * (ell * ‖y‖) ≤ 1 * (ell * ‖y‖) :=
        mul_le_mul_of_nonneg_right hs.2 (mul_nonneg hell (norm_nonneg y))
      _ ≤ ‖y‖ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hell1 (norm_nonneg y)
  exact hle.trans_lt (hy'.trans_le hrho)

end

end GlobalEmbedding.Offline
