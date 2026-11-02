import Smoothing.TensorSmoothingRegularity

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

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {n : ℕ} {V : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]

/-- One literal scalar entry of the transported global tensor smoothing. -/
def tensorSmoothingEntry (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (p i : Fin A.count) (a d r s : Fin n) (y : E) : ℝ :=
  chi i ((A.chart p).symm y) ^ 2 *
    (tensorFrameTransition A b p i a r y * tensorFrameTransition A b p i d s y) *
    bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b H i) i
      (A.chart i ((A.chart p).symm y)) (finProdFinEquiv (r, s))

/-- The actual local tensor convolution is smooth on its true buffer. -/
theorem tensorLocalSmoothing_contDiffOn (A : BufferedAtlas M E) (mu : Measure E)
    [mu.IsAddHaarMeasure] {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (i : Fin A.count)
    (hH : ContDiffOn ℝ ∞ (tensorCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target) :
    ContDiffOn ℝ ∞ (bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b H i) i)
      (bufferedInnerCoordinates A i) := by
  have hExt := tensorCoordinateExtension_contDiffOn A b H i hH
  apply signedSmoothing_contDiffOn mu hK hcompact (bufferedInnerCoordinates_open A i)
    (A.chart i).open_target hExt ell ?_
  intro z hz y hy
  simpa only [one_smul] using buffered_kernel_segment A i hsupp hrho hell hell1 hz hy
    (s := 1) (by simp)

/-- Each transported scalar entry is smooth on its actual active overlap. -/
theorem tensorSmoothingEntry_contDiffOn (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (p i : Fin A.count)
    (hH : ContDiffOn ℝ ∞ (tensorCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target)
    (hframe : ∀ a r, ContDiffOn ℝ ∞ (tensorFrameTransition A b p i a r)
      (bufferedChartOverlap A p i)) (a d r s : Fin n) :
    ContDiffOn ℝ ∞ (tensorSmoothingEntry A mu K ell chi b H p i a d r s)
      (bufferedChartOverlap A p i) := by
  have hw : ContDiffOn ℝ ∞ (chi i ∘ (A.chart p).symm) (bufferedChartOverlap A p i) :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem p))).contDiffOn.mono
      (fun _ hz => hz.1)
  have herror := tensorLocalSmoothing_contDiffOn A mu hK hcompact hsupp hrho hell hell1 b H i hH
  have heval : ContDiffOn ℝ ∞
      (fun y => bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b H i) i y
        (finProdFinEquiv (r, s))) (bufferedInnerCoordinates A i) := (contDiffOn_pi.mp herror) _
  exact ((hw.pow 2).mul ((hframe a r).mul (hframe d s))).mul
    (heval.comp (bufferedTransition_contDiffOn A hA p i) (bufferedTransition_maps A p i))

/-- The scalar tensor summand has a genuine zero germ outside its original
cutoff support, regardless of local coefficient or frame values elsewhere. -/
theorem tensorSmoothingEntry_eventuallyEq_zero (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (p i : Fin A.count)
    (a d r s : Fin n) {y : E} (hy : y ∈ (A.chart p).target)
    (hi : (A.chart p).symm y ∉ tsupport (chi i)) :
    tensorSmoothingEntry A mu K ell chi b H p i a d r s =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
  filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hi).comp_tendsto
    ((A.chart p).symm.continuousAt hy)] with z hz
  change chi i ((A.chart p).symm z) = 0 at hz
  simp only [tensorSmoothingEntry, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]

/-- In every receiving frame the SAME actual smoothed tensor is the sum of
true local convolutions with both frame-change factors. -/
theorem bufferedTensorSmoothing_chart_eq (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (p : Fin A.count) (a d : Fin n) :
    (fun y => tensorFrameComponents (b p ((A.chart p).symm y))
      (bufferedTensorSmoothing A mu K ell chi b H ((A.chart p).symm y))
        (finProdFinEquiv (a, d))) =
      fun y => ∑ i, ∑ r, ∑ s, tensorSmoothingEntry A mu K ell chi b H p i a d r s y := by
  funext y
  simp only [tensorFrameComponents, Equiv.symm_apply_apply, bufferedTensorSmoothing,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : chi i ((A.chart p).symm y) = 0
  · simp only [tensorSmoothingEntry, hi, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_mul, Finset.sum_const_zero]
  · have hx := A.inner_subset i (hchiSupport i (subset_tsupport (chi i) hi))
    simp only [bufferedChartSmoothing, Set.indicator_of_mem hx, Function.comp_apply]
    rw [tensorFromFrameComponents, Matrix.toBilin_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    unfold tensorSmoothingEntry tensorFrameTransition
    ring

end

end GlobalEmbedding.Offline
