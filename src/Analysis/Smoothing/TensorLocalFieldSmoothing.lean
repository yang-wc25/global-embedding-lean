import Smoothing.TensorLocalCharts

/-!
# Actual tensor convolution for a chart family covering only a parameter region

The field is a genuine dependent bilinear tensor, reconstructed after the
same actual local integrals. Its receiving coordinates are jointly smooth.
The error identity needs the square partition only at the evaluation point,
and hence on the genuine neighborhood produced by local normalization.
No global-cover premise is introduced.
-/

open Module MeasureTheory Manifold IsManifold GlobalEmbedding.Paper Function Set Filter
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι X E : Type*} [Fintype ι] [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {n : ℕ} {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]

def tensorLocalFieldCoefficients (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x)) (i : ι) (x : X) : Fin (n*n) → ℝ :=
  tensorFrameComponents (b i x) (H x)

def tensorLocalFieldSmoothing (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → X → ℝ)
    (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x)) (x : X) : LinearMap.BilinForm ℝ (V x) :=
  ∑ i, chi i x ^ 2 • tensorFromFrameComponents (b i x)
    (tensorLocalChartConvolution C mu K ell (tensorLocalFieldCoefficients b H i) i x)

/-- When a global atlas is available this is literally the already proved
operator, not a second field with separately glued jets. -/
theorem tensorLocalFieldSmoothing_eq_buffered (A : BufferedAtlas X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → X → ℝ)
    (b : Fin A.count → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x)) :
    tensorLocalFieldSmoothing (tensorChartFamilyOfAtlas A) mu K ell chi b H =
      bufferedTensorSmoothing A mu K ell chi b H := rfl

/-- Exact local error identity requires the genuine partition only HERE. -/
theorem tensorLocalFieldSmoothing_error_at
    (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → X → ℝ)
    (hsupport : ∀ i, tsupport (chi i) ⊆ C.inner i)
    (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x)) (x : X)
    (hpartition : ∑ i, chi i x ^ 2 = 1) :
    tensorLocalFieldSmoothing C mu K ell chi b H x - H x =
      ∑ i, chi i x ^ 2 • tensorFromFrameComponents (b i x)
        (tensorLocalConvolution C mu K ell (tensorLocalFieldCoefficients b H i) i (C.chart i x) -
          tensorLocalCoordinateExtension C (tensorLocalFieldCoefficients b H i) i (C.chart i x)) := by
  have hsingle (i : ι) :
      chi i x ^ 2 • tensorFromFrameComponents (b i x)
        (tensorLocalChartConvolution C mu K ell (tensorLocalFieldCoefficients b H i) i x) -
        chi i x ^ 2 • H x =
      chi i x ^ 2 • tensorFromFrameComponents (b i x)
        (tensorLocalConvolution C mu K ell (tensorLocalFieldCoefficients b H i) i (C.chart i x) -
          tensorLocalCoordinateExtension C (tensorLocalFieldCoefficients b H i) i (C.chart i x)) := by
    by_cases hi : chi i x = 0
    · simp only [hi, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_smul]
      exact sub_self (0 : LinearMap.BilinForm ℝ (V x))
    · have hx := C.inner_subset i (hsupport i (subset_tsupport (chi i) hi))
      have hext : tensorLocalCoordinateExtension C (tensorLocalFieldCoefficients b H i) i
          (C.chart i x) = tensorFrameComponents (b i x) (H x) := by
        simp only [tensorLocalCoordinateExtension, Set.indicator_of_mem ((C.chart i).map_source hx),
          Function.comp_apply]
        exact congrArg (tensorLocalFieldCoefficients b H i) ((C.chart i).left_inv hx)
      rw [hext, tensorFromFrameComponents_sub, tensorFromFrameComponents_components]
      simp only [tensorLocalChartConvolution, Set.indicator_of_mem hx, Function.comp_apply]
      exact (smul_sub (chi i x ^ 2)
        (tensorFromFrameComponents (b i x)
          (tensorLocalConvolution C mu K ell (tensorLocalFieldCoefficients b H i) i (C.chart i x)))
        (H x)).symm
  have hsum : (∑ i, chi i x ^ 2 • H x) = H x := by
    rw [← Finset.sum_smul, hpartition, one_smul]
  unfold tensorLocalFieldSmoothing
  conv_lhs => rw [← hsum]
  calc
    _ = ∑ i, (chi i x ^ 2 • tensorFromFrameComponents (b i x)
        (tensorLocalChartConvolution C mu K ell (tensorLocalFieldCoefficients b H i) i x) -
          chi i x ^ 2 • H x) :=
      (Finset.sum_sub_distrib (s := Finset.univ)
        (fun i => chi i x ^ 2 • tensorFromFrameComponents (b i x)
          (tensorLocalChartConvolution C mu K ell (tensorLocalFieldCoefficients b H i) i x))
        (fun i => chi i x ^ 2 • H x)).symm
    _ = _ := Finset.sum_congr rfl (fun i _ => hsingle i)

def tensorLocalFrameTransition (C : TensorBufferedChartFamily ι X E)
    (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (p i : ι) (a r : Fin n) (y : E) : ℝ :=
  (b i ((C.chart p).symm y)).repr (b p ((C.chart p).symm y) a) r

def tensorLocalChartOverlap (C : TensorBufferedChartFamily ι X E) (p i : ι) : Set E :=
  (C.chart p).target ∩ (C.chart p).symm ⁻¹' C.inner i

theorem tensorLocalChartOverlap_open (C : TensorBufferedChartFamily ι X E) (p i : ι) :
    IsOpen (tensorLocalChartOverlap C p i) :=
  (C.chart p).isOpen_inter_preimage_symm (C.inner_open i)

def tensorLocalFieldEntry (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → X → ℝ)
    (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x))
    (p i : ι) (a d r s : Fin n) (y : E) : ℝ :=
  chi i ((C.chart p).symm y) ^ 2 *
    (tensorLocalFrameTransition C b p i a r y * tensorLocalFrameTransition C b p i d s y) *
    tensorLocalConvolution C mu K ell (tensorLocalFieldCoefficients b H i) i
      (C.chart i ((C.chart p).symm y)) (finProdFinEquiv (r, s))

/-- Full two-frame contraction in the actual receiving coordinates. -/
theorem tensorLocalFieldSmoothing_chart_eq
    (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → X → ℝ)
    (hsupport : ∀ i, tsupport (chi i) ⊆ C.inner i)
    (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x)) (p : ι) (a d : Fin n) :
    (fun y => tensorFrameComponents (b p ((C.chart p).symm y))
      (tensorLocalFieldSmoothing C mu K ell chi b H ((C.chart p).symm y))
        (finProdFinEquiv (a, d))) =
      fun y => ∑ i, ∑ r, ∑ s, tensorLocalFieldEntry C mu K ell chi b H p i a d r s y := by
  funext y
  simp only [tensorFrameComponents, Equiv.symm_apply_apply, tensorLocalFieldSmoothing,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : chi i ((C.chart p).symm y) = 0
  · simp only [tensorLocalFieldEntry, hi, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_mul, Finset.sum_const_zero]
  · have hx := C.inner_subset i (hsupport i (subset_tsupport (chi i) hi))
    simp only [tensorLocalChartConvolution, Set.indicator_of_mem hx, Function.comp_apply]
    rw [tensorFromFrameComponents, Matrix.toBilin_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    unfold tensorLocalFieldEntry tensorLocalFrameTransition
    ring

variable [BorelSpace E] [FiniteDimensional ℝ E]
  [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]

/-- True coordinate smoothness of the actual tensor reconstruction in each
receiving chart of a possibly noncovering family. The frame premise is the
actual transition function, not an independently supplied coordinate field. -/
theorem tensorLocalFieldSmoothing_coordinates_contDiffOn
    (C : TensorBufferedChartFamily ι X E)
    (hchart : ∀ i, C.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ X)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ C.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : ι → X → ℝ) (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hsupport : ∀ i, tsupport (chi i) ⊆ C.inner i)
    (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (tensorLocalFieldCoefficients b H i ∘ (C.chart i).symm) (C.chart i).target)
    (hframe : ∀ p i a r, ContDiffOn ℝ ∞ (tensorLocalFrameTransition C b p i a r)
      (tensorLocalChartOverlap C p i)) (p : ι) :
    ContDiffOn ℝ ∞ (fun y => tensorFrameComponents (b p ((C.chart p).symm y))
      (tensorLocalFieldSmoothing C mu K ell chi b H ((C.chart p).symm y))) (C.chart p).target := by
  apply contDiffOn_pi.mpr
  intro k
  obtain ⟨⟨a, d⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [tensorLocalFieldSmoothing_chart_eq C mu K ell chi hsupport b H p a d]
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro r _
  apply ContDiffOn.sum
  intro s _
  intro y hy
  by_cases hi : (C.chart p).symm y ∈ tsupport (chi i)
  · have hyO : y ∈ tensorLocalChartOverlap C p i := ⟨hy, hsupport i hi⟩
    have hw : ContDiffOn ℝ ∞ (chi i ∘ (C.chart p).symm) (tensorLocalChartOverlap C p i) :=
      ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hchart p))).contDiffOn.mono
        (fun _ h => h.1)
    have ht : ContDiffOn ℝ ∞ (C.chart i ∘ (C.chart p).symm) (tensorLocalChartOverlap C p i) :=
      ((contMDiffOn_of_mem_maximalAtlas (hchart i)).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas (hchart p)).mono (fun _ h => h.1))
        (fun _ h => C.inner_subset i h.2)).contDiffOn
    have hs := tensorLocalConvolution_contDiffOn C mu hK hcompact hsupp hrho hell hell1
      (tensorLocalFieldCoefficients b H i) i (hH i)
    have hg := (contDiffOn_pi.mp hs) (finProdFinEquiv (r, s))
    have hentry : ContDiffOn ℝ ∞ (tensorLocalFieldEntry C mu K ell chi b H p i a d r s)
        (tensorLocalChartOverlap C p i) :=
      ((hw.pow 2).mul ((hframe p i a r).mul (hframe p i d s))).mul
        (hg.comp ht (fun z hz => tensorLocalInner_mem C i hz.2))
    exact (hentry.contDiffAt ((tensorLocalChartOverlap_open C p i).mem_nhds hyO)).contDiffWithinAt
  · have he : tensorLocalFieldEntry C mu K ell chi b H p i a d r s =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hi).comp_tendsto
        ((C.chart p).symm.continuousAt hy)] with z hz
      change chi i ((C.chart p).symm z) = 0 at hz
      simp only [tensorLocalFieldEntry, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

end
end GlobalEmbedding.Offline
