import Smoothing.TensorSmoothing
import Smoothing.TensorTransferJets

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

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {n : ℕ} {V : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]

/-- The genuine frame-change coefficient in one receiving source chart. -/
def tensorFrameTransition (A : BufferedAtlas M E)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (p i : Fin A.count) (a r : Fin n) (y : E) : ℝ :=
  (b i ((A.chart p).symm y)).repr (b p ((A.chart p).symm y) a) r

/-- One literal scalar entry of the transported global tensor error. -/
def tensorErrorEntry (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (p i : Fin A.count) (a d r s : Fin n) (y : E) : ℝ :=
  chi i ((A.chart p).symm y) ^ 2 *
    (tensorFrameTransition A b p i a r y * tensorFrameTransition A b p i d s y) *
    bufferedLocalError A mu K ell (tensorCoefficientField A b H i) i
      (A.chart i ((A.chart p).symm y)) (finProdFinEquiv (r, s))

/-- Local tensor coefficients need smoothness only in their genuine chart.
No fictitious global smoothness of a zero extension is required. -/
theorem tensorCoordinateExtension_contDiffOn (A : BufferedAtlas M E)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (i : Fin A.count)
    (hH : ContDiffOn ℝ ∞ (tensorCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target) :
    ContDiffOn ℝ ∞ (bufferedCoordinateExtension A (tensorCoefficientField A b H i) i)
      (A.chart i).target := by
  intro z hz
  exact ((hH.contDiffAt ((A.chart i).open_target.mem_nhds hz)).congr_of_eventuallyEq
    (bufferedCoordinateExtension_eventuallyEq A _ i hz)).contDiffWithinAt

/-- The actual local tensor convolution error is smooth on its true buffer. -/
theorem tensorLocalError_contDiffOn (A : BufferedAtlas M E) (mu : Measure E)
    [mu.IsAddHaarMeasure] {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (i : Fin A.count)
    (hH : ContDiffOn ℝ ∞ (tensorCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target) :
    ContDiffOn ℝ ∞ (bufferedLocalError A mu K ell (tensorCoefficientField A b H i) i)
      (bufferedInnerCoordinates A i) := by
  have hExt := tensorCoordinateExtension_contDiffOn A b H i hH
  apply (signedSmoothing_contDiffOn mu hK hcompact (bufferedInnerCoordinates_open A i)
    (A.chart i).open_target hExt ell ?_).sub (hExt.mono (fun _ hz => hz.1))
  intro z hz y hy
  simpa only [one_smul] using buffered_kernel_segment A i hsupp hrho hell hell1 hz hy
    (s := 1) (by simp)

/-- Each transported scalar entry is smooth on its actual active overlap. -/
theorem tensorErrorEntry_contDiffOn (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
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
    ContDiffOn ℝ ∞ (tensorErrorEntry A mu K ell chi b H p i a d r s)
      (bufferedChartOverlap A p i) := by
  have hw : ContDiffOn ℝ ∞ (chi i ∘ (A.chart p).symm) (bufferedChartOverlap A p i) :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem p))).contDiffOn.mono
      (fun _ hz => hz.1)
  have herror := tensorLocalError_contDiffOn A mu hK hcompact hsupp hrho hell hell1 b H i hH
  have heval : ContDiffOn ℝ ∞
      (fun y => bufferedLocalError A mu K ell (tensorCoefficientField A b H i) i y
        (finProdFinEquiv (r, s))) (bufferedInnerCoordinates A i) := (contDiffOn_pi.mp herror) _
  exact ((hw.pow 2).mul ((hframe a r).mul (hframe d s))).mul
    (heval.comp (bufferedTransition_contDiffOn A hA p i) (bufferedTransition_maps A p i))

/-- The scalar tensor summand has a genuine zero germ outside its original
cutoff support, regardless of local coefficient or frame values elsewhere. -/
theorem tensorErrorEntry_eventuallyEq_zero (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (p i : Fin A.count)
    (a d r s : Fin n) {y : E} (hy : y ∈ (A.chart p).target)
    (hi : (A.chart p).symm y ∉ tsupport (chi i)) :
    tensorErrorEntry A mu K ell chi b H p i a d r s =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
  filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hi).comp_tendsto
    ((A.chart p).symm.continuousAt hy)] with z hz
  change chi i ((A.chart p).symm z) = 0 at hz
  simp only [tensorErrorEntry, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]

/-- The same actual tensor error in a receiving chart equals the exact sum
whose jets are estimated. No separately glued jet field is used. -/
theorem bufferedTensorSmoothing_error_chart_eq (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (p : Fin A.count) (a d : Fin n) :
    (fun y => tensorFrameComponents (b p ((A.chart p).symm y))
      (bufferedTensorSmoothing A mu K ell chi b H ((A.chart p).symm y) - H ((A.chart p).symm y))
        (finProdFinEquiv (a, d))) =
      fun y => ∑ i, ∑ r, ∑ s, tensorErrorEntry A mu K ell chi b H p i a d r s y := by
  funext y
  rw [bufferedTensorSmoothing_error_components A mu K ell chi hchiSupport hpartition b H]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold tensorErrorEntry tensorFrameTransition bufferedLocalError
  simp only [Pi.sub_apply]
  ring

end

end GlobalEmbedding.Offline
