import Smoothing.TensorLocalModelDomains

/-!
# Actual tensor smoothing in every receiving frame

Source: buffered tensor localization for (6.4). Smoothness is required only
on actual chart domains; the raw outside extensions and frame choices need
not be smooth. Every inactive summand has a genuine zero germ. The active
summands use the real transition and both real frame coefficients.
-/

open Module MeasureTheory GlobalEmbedding.Paper Function Set Filter Manifold IsManifold
open scoped BigOperators ContDiff Topology

namespace GlobalEmbedding.Offline

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {ι E M : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {n : ℕ} {V : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]

/-- One literal scalar entry of the transported global tensor smoothing. -/
def tensorLocalSmoothingEntry (A : TensorBufferedChartFamily ι M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → M → ℝ)
    (b : ι → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (p i : ι) (a d r s : Fin n) (y : E) : ℝ :=
  chi i ((A.chart p).symm y) ^ 2 *
    (tensorLocalFrameTransition A b p i a r y * tensorLocalFrameTransition A b p i d s y) *
    tensorLocalConvolution A mu K ell (tensorLocalCoefficientField A b H i) i
      (A.chart i ((A.chart p).symm y)) (finProdFinEquiv (r, s))

/-- The actual local tensor convolution is smooth on its true buffer. -/
theorem tensorFamilyLocalSmoothing_contDiffOn (A : TensorBufferedChartFamily ι M E) (mu : Measure E)
    [mu.IsAddHaarMeasure] {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (b : ι → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (i : ι)
    (hH : ContDiffOn ℝ ∞ (tensorLocalCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target) :
    ContDiffOn ℝ ∞ (tensorLocalConvolution A mu K ell (tensorLocalCoefficientField A b H i) i)
      (tensorLocalInner A i) := by
  have hExt := tensorLocalCoordinateExtension_contDiffOn A (tensorLocalCoefficientField A b H i) i hH
  apply signedSmoothing_contDiffOn mu hK hcompact (tensorLocalInner_open A i)
    (A.chart i).open_target hExt ell ?_
  intro z hz y hy
  simpa only [one_smul] using tensorLocal_kernel_segment A i hsupp hrho hell hell1 hz hy
    (s := 1) (by simp)

/-- Each transported scalar entry is smooth on its actual active overlap. -/
theorem tensorLocalSmoothingEntry_contDiffOn (A : TensorBufferedChartFamily ι M E) (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : ι → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (b : ι → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (p i : ι)
    (hH : ContDiffOn ℝ ∞ (tensorLocalCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target)
    (hframe : ∀ a r, ContDiffOn ℝ ∞ (tensorLocalFrameTransition A b p i a r)
      (tensorLocalChartOverlap A p i)) (a d r s : Fin n) :
    ContDiffOn ℝ ∞ (tensorLocalSmoothingEntry A mu K ell chi b H p i a d r s)
      (tensorLocalChartOverlap A p i) := by
  have hw : ContDiffOn ℝ ∞ (chi i ∘ (A.chart p).symm) (tensorLocalChartOverlap A p i) :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA p))).contDiffOn.mono
      (fun _ hz => hz.1)
  have herror := tensorFamilyLocalSmoothing_contDiffOn A mu hK hcompact hsupp hrho hell hell1 b H i hH
  have heval : ContDiffOn ℝ ∞
      (fun y => tensorLocalConvolution A mu K ell (tensorLocalCoefficientField A b H i) i y
        (finProdFinEquiv (r, s))) (tensorLocalInner A i) := (contDiffOn_pi.mp herror) _
  exact ((hw.pow 2).mul ((hframe a r).mul (hframe d s))).mul
    (heval.comp (tensorLocalTransition_contDiffOn A hA p i) ((fun z hz => tensorLocalInner_mem A i hz.2)))

/-- The scalar tensor summand has a genuine zero germ outside its original
cutoff support, regardless of local coefficient or frame values elsewhere. -/
theorem tensorLocalSmoothingEntry_eventuallyEq_zero (A : TensorBufferedChartFamily ι M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → M → ℝ)
    (b : ι → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (p i : ι)
    (a d r s : Fin n) {y : E} (hy : y ∈ (A.chart p).target)
    (hi : (A.chart p).symm y ∉ tsupport (chi i)) :
    tensorLocalSmoothingEntry A mu K ell chi b H p i a d r s =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
  filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hi).comp_tendsto
    ((A.chart p).symm.continuousAt hy)] with z hz
  change chi i ((A.chart p).symm z) = 0 at hz
  simp only [tensorLocalSmoothingEntry, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]

/-- In every receiving frame the SAME actual smoothed tensor is the sum of
true local convolutions with both frame-change factors. -/
theorem tensorFamilySmoothing_chart_eq (A : TensorBufferedChartFamily ι M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (b : ι → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (p : ι) (a d : Fin n) :
    (fun y => tensorFrameComponents (b p ((A.chart p).symm y))
      (tensorLocalFieldSmoothing A mu K ell chi b H ((A.chart p).symm y))
        (finProdFinEquiv (a, d))) =
      fun y => ∑ i, ∑ r, ∑ s, tensorLocalSmoothingEntry A mu K ell chi b H p i a d r s y := by
  funext y
  simp only [tensorFrameComponents, Equiv.symm_apply_apply, tensorLocalFieldSmoothing,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : chi i ((A.chart p).symm y) = 0
  · simp only [tensorLocalSmoothingEntry, hi, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_mul, Finset.sum_const_zero]
  · have hx := A.inner_subset i (hchiSupport i (subset_tsupport (chi i) hi))
    simp only [tensorLocalChartConvolution, Set.indicator_of_mem hx, Function.comp_apply]
    rw [tensorFromFrameComponents, Matrix.toBilin_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    unfold tensorLocalSmoothingEntry tensorLocalFrameTransition tensorLocalCoefficientField
    ring

end

end GlobalEmbedding.Offline
