import Smoothing.TensorLocalErrorJets

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

variable {ι E M : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]

/-- The fixed genuine buffer sampled by all admissible scales. -/
def tensorLocalSamplingCoordinates (A : TensorBufferedChartFamily ι M E) (i : ι) : Set E :=
  ⋃ z ∈ tensorLocalInner A i, Metric.ball z A.buffer

omit [NormedSpace ℝ E] in
/-- The sampling buffer is open, without any compactness assumption. -/
theorem tensorLocalSamplingCoordinates_open (A : TensorBufferedChartFamily ι M E) (i : ι) :
    IsOpen (tensorLocalSamplingCoordinates A i) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

omit [NormedSpace ℝ E] in
/-- The original inner coordinates lie in the fixed sampling buffer. -/
theorem tensorLocalInner_subset_sampling (A : TensorBufferedChartFamily ι M E) (i : ι) :
    tensorLocalInner A i ⊆ tensorLocalSamplingCoordinates A i := by
  intro z hz
  exact mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, by simpa only [mem_ball, dist_self] using A.buffer_pos⟩⟩

omit [NormedSpace ℝ E] in
/-- The entire fixed sampling buffer lies inside the ORIGINAL chart target. -/
theorem tensorLocalSampling_subset_target (A : TensorBufferedChartFamily ι M E) (i : ι) :
    tensorLocalSamplingCoordinates A i ⊆ (A.chart i).target := by
  intro y hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp hy
  obtain ⟨hzInner, hyball⟩ := mem_iUnion.mp hz
  apply A.buffered i ((A.chart i).symm z) hzInner.2
  simpa only [(A.chart i).right_inv hzInner.1] using hyball

/-- Every actual convolution/Taylor segment lies in that same scale-independent
sampling buffer, derived from its definition and the original common radius. -/
theorem tensorLocal_kernel_segment_mem_sampling (A : TensorBufferedChartFamily ι M E) (i : ι)
    {K : E → ℝ} {rho ell : ℝ} (hK : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    {z : E} (hz : z ∈ tensorLocalInner A i)
    {y : E} (hy : y ∈ tsupport K) {s : ℝ} (hs : s ∈ Icc 0 1) :
    z - s • (ell • y) ∈ tensorLocalSamplingCoordinates A i := by
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


variable {q d n : ℕ} {V : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]

/-- Actual evaluation near the region on which the square partition is valid. -/
def tensorLocalEvaluation (A : TensorBufferedChartFamily ι M E) (U : Set M) (i : ι) : Set E :=
  tensorLocalInner A i ∩ (A.chart i).symm ⁻¹' U

def tensorLocalModelTargets (A : TensorBufferedChartFamily ι M E) (c : E ≃L[ℝ] (Fin d → ℝ)) :=
  modelCoordinateDomains c (fun i => (A.chart i).target)

def tensorLocalModelEvaluation (A : TensorBufferedChartFamily ι M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (U : Set M) :=
  modelCoordinateDomains c (tensorLocalEvaluation A U)

def tensorLocalModelInner (A : TensorBufferedChartFamily ι M E) (c : E ≃L[ℝ] (Fin d → ℝ)) :=
  modelCoordinateDomains c (tensorLocalInner A)

def tensorLocalModelSampling (A : TensorBufferedChartFamily ι M E) (c : E ≃L[ℝ] (Fin d → ℝ)) :=
  modelCoordinateDomains c (tensorLocalSamplingCoordinates A)

def tensorLocalCoefficientField (A : TensorBufferedChartFamily ι M E)
    (b : ι → (x : M) → Module.Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (i : ι) : M → Fin (n*n) → ℝ :=
  tensorLocalFieldCoefficients b H i

def tensorLocalNativeCoordinates (A : TensorBufferedChartFamily ι M E)
    (b : ι → (x : M) → Module.Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) :=
  fun i : ι => tensorLocalCoefficientField A b H i ∘ (A.chart i).symm

def tensorLocalModelCoordinates (A : TensorBufferedChartFamily ι M E)
    (c : E ≃L[ℝ] (Fin d → ℝ))
    (b : ι → (x : M) → Module.Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) :=
  modelCoordinateFamily c (tensorLocalNativeCoordinates A b H)

theorem tensorLocalModelTargets_open (A : TensorBufferedChartFamily ι M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (i : ι) : IsOpen (tensorLocalModelTargets A c i) :=
  modelCoordinateDomains_open c (fun i => (A.chart i).open_target) i

theorem tensorLocalModelSampling_subset_target (A : TensorBufferedChartFamily ι M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (i : ι) :
    tensorLocalModelSampling A c i ⊆ tensorLocalModelTargets A c i :=
  fun _ hx => tensorLocalSampling_subset_target A i hx

theorem tensorLocalModelEvaluation_subset_target (A : TensorBufferedChartFamily ι M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (U : Set M) (i : ι) :
    tensorLocalModelEvaluation A c U i ⊆ tensorLocalModelTargets A c i :=
  fun _ hx => hx.1.1

theorem tensorLocalModelInner_subset_target (A : TensorBufferedChartFamily ι M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (i : ι) :
    tensorLocalModelInner A c i ⊆ tensorLocalModelTargets A c i := fun _ hx => hx.1

theorem tensorLocalModelCoordinates_contDiffOn (A : TensorBufferedChartFamily ι M E)
    (c : E ≃L[ℝ] (Fin d → ℝ))
    (b : ι → (x : M) → Module.Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (tensorLocalCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target) (i : ι) :
    ContDiffOn ℝ ∞ (tensorLocalModelCoordinates A c b H i) (tensorLocalModelTargets A c i) :=
  modelCoordinateFamily_contDiffOn c hH i

theorem iteratedFDeriv_tensorLocalCoordinateExtension
    (A : TensorBufferedChartFamily ι M E) (u : M → Fin q → ℝ) (i : ι) (k : ℕ)
    {z : E} (hz : z ∈ (A.chart i).target) :
    iteratedFDeriv ℝ k (tensorLocalCoordinateExtension A u i) z =
      iteratedFDeriv ℝ k (u ∘ (A.chart i).symm) z :=
  ((tensorLocalCoordinateExtension_eventuallyEq A u i hz).iteratedFDeriv ℝ k).eq_of_nhds

end
end GlobalEmbedding.Offline
