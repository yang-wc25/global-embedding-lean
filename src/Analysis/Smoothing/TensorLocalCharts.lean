import Smoothing.TensorLocalNormalizationBounds
import Smoothing.TensorParameterLinearity

/-!
# Buffered finite chart families without a global-cover field

The parameter charts of the frozen original ABI need cover only the stated
compact evaluation set. This record retains the actual charts, inner domains
and common buffer, and deliberately has no assertion that they cover X.
Actual convolution and its local regularity therefore need no fictitious
global finite parameter atlas.
-/

open Module MeasureTheory Manifold IsManifold GlobalEmbedding.Paper Function Set Filter
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

structure TensorBufferedChartFamily (ι X E : Type*) [TopologicalSpace X] [PseudoMetricSpace E] where
  chart : ι → OpenPartialHomeomorph X E
  inner : ι → Set X
  inner_open : ∀ i, IsOpen (inner i)
  inner_subset : ∀ i, inner i ⊆ (chart i).source
  buffer : ℝ
  buffer_pos : 0 < buffer
  buffered : ∀ i x, x ∈ inner i → Metric.ball (chart i x) buffer ⊆ (chart i).target

variable {ι X E F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Forget the global cover of an already prepared atlas; charts do not change. -/
def tensorChartFamilyOfAtlas (A : BufferedAtlas X E) : TensorBufferedChartFamily (Fin A.count) X E where
  chart := A.chart
  inner := A.inner
  inner_open := A.inner_open
  inner_subset := A.inner_subset
  buffer := A.buffer
  buffer_pos := A.buffer_pos
  buffered := A.buffered

def tensorLocalInner (C : TensorBufferedChartFamily ι X E) (i : ι) : Set E :=
  (C.chart i).target ∩ (C.chart i).symm ⁻¹' C.inner i

theorem tensorLocalInner_open (C : TensorBufferedChartFamily ι X E) (i : ι) :
    IsOpen (tensorLocalInner C i) :=
  (C.chart i).isOpen_inter_preimage_symm (C.inner_open i)

theorem tensorLocalInner_mem (C : TensorBufferedChartFamily ι X E) (i : ι)
    {x : X} (hx : x ∈ C.inner i) : C.chart i x ∈ tensorLocalInner C i := by
  exact ⟨(C.chart i).map_source (C.inner_subset i hx), by
    simpa only [Set.mem_preimage, (C.chart i).left_inv (C.inner_subset i hx)] using hx⟩

def tensorLocalCoordinateExtension (C : TensorBufferedChartFamily ι X E)
    (u : X → F) (i : ι) : E → F :=
  (C.chart i).target.indicator (u ∘ (C.chart i).symm)

theorem tensorLocalCoordinateExtension_eventuallyEq
    (C : TensorBufferedChartFamily ι X E) (u : X → F) (i : ι)
    {z : E} (hz : z ∈ (C.chart i).target) :
    tensorLocalCoordinateExtension C u i =ᶠ[𝓝 z] (u ∘ (C.chart i).symm) := by
  filter_upwards [(C.chart i).open_target.mem_nhds hz] with y hy
  exact Set.indicator_of_mem hy _

theorem tensorLocalCoordinateExtension_contDiffOn
    (C : TensorBufferedChartFamily ι X E) (u : X → F) (i : ι)
    (hu : ContDiffOn ℝ ∞ (u ∘ (C.chart i).symm) (C.chart i).target) :
    ContDiffOn ℝ ∞ (tensorLocalCoordinateExtension C u i) (C.chart i).target := by
  intro z hz
  exact ((hu.contDiffAt ((C.chart i).open_target.mem_nhds hz)).congr_of_eventuallyEq
    (tensorLocalCoordinateExtension_eventuallyEq C u i hz)).contDiffWithinAt

/-- Every actual kernel segment stays in its original parameter/source chart.
No cover, compactness of X, or global regularity of the indicator is used. -/
theorem tensorLocal_kernel_segment (C : TensorBufferedChartFamily ι X E) (i : ι)
    {K : E → ℝ} {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ C.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    {z : E} (hz : z ∈ tensorLocalInner C i) {y : E} (hy : y ∈ tsupport K)
    {s : ℝ} (hs : s ∈ Icc 0 1) : z - s • (ell • y) ∈ (C.chart i).target := by
  apply C.buffered i ((C.chart i).symm z) hz.2
  change dist (z - s • (ell • y)) (C.chart i ((C.chart i).symm z)) < C.buffer
  rw [(C.chart i).right_inv hz.1, dist_eq_norm, sub_sub_cancel_left, norm_neg]
  have hy' : ‖y‖ < rho := by simpa only [Metric.mem_ball, dist_zero_right] using hsupp hy
  have hle : ‖s • (ell • y)‖ ≤ ‖y‖ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hs.1, abs_of_nonneg hell]
    calc
      s * (ell * ‖y‖) ≤ 1 * (ell * ‖y‖) :=
        mul_le_mul_of_nonneg_right hs.2 (mul_nonneg hell (norm_nonneg _))
      _ ≤ ‖y‖ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hell1 (norm_nonneg y)
  exact hle.trans_lt (hy'.trans_le hrho)

variable [MeasurableSpace E]

def tensorLocalConvolution (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (u : X → F) (i : ι) : E → F :=
  signedSmoothing mu K ell (tensorLocalCoordinateExtension C u i)

def tensorLocalChartConvolution (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (u : X → F) (i : ι) : X → F :=
  (C.chart i).source.indicator (tensorLocalConvolution C mu K ell u i ∘ C.chart i)

variable [BorelSpace E] [FiniteDimensional ℝ E]

/-- The actual local convolution of original chart coefficients is smooth
on the true inner chart, even for a family covering only a neighborhood of K. -/
theorem tensorLocalConvolution_contDiffOn
    (C : TensorBufferedChartFamily ι X E) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ C.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (u : X → F) (i : ι)
    (hu : ContDiffOn ℝ ∞ (u ∘ (C.chart i).symm) (C.chart i).target) :
    ContDiffOn ℝ ∞ (tensorLocalConvolution C mu K ell u i) (tensorLocalInner C i) := by
  apply signedSmoothing_contDiffOn mu hK hcompact (tensorLocalInner_open C i)
    (C.chart i).open_target (tensorLocalCoordinateExtension_contDiffOn C u i hu) ell
  intro z hz y hy
  simpa only [one_smul] using tensorLocal_kernel_segment C i hsupp hrho hell hell1 hz hy
    (s := 1) (by simp)

variable [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]

/-- Global smoothness of the literal cutoff local-convolution term needs
smoothness of u only in its actual source chart, not a global cover of X. -/
theorem tensorLocalWeightedConvolution_contMDiff
    (C : TensorBufferedChartFamily ι X E)
    (hchart : ∀ i, C.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ X)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ C.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : ι → X → ℝ) (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hsupport : ∀ i, tsupport (chi i) ⊆ C.inner i)
    (u : X → F) (i : ι)
    (hu : ContDiffOn ℝ ∞ (u ∘ (C.chart i).symm) (C.chart i).target) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞
      (fun x => chi i x ^ 2 • tensorLocalChartConvolution C mu K ell u i x) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hterm : tsupport (fun x => chi i x ^ 2 • tensorLocalChartConvolution C mu K ell u i x)
      ⊆ tsupport (chi i) := by
    apply (tsupport_smul_subset_left _ _).trans
    simpa only [pow_two] using (tsupport_mul_subset_left (f := chi i) (g := chi i))
  have hi := hsupport i (hterm hx)
  have hs := tensorLocalConvolution_contDiffOn C mu hK hcompact hsupp hrho hell hell1 u i hu
  have hsat := (hs.contDiffAt ((tensorLocalInner_open C i).mem_nhds (tensorLocalInner_mem C i hi))).contMDiffAt
  have hc := hsat.comp x (contMDiffAt_of_mem_maximalAtlas (hchart i) (C.inner_subset i hi))
  have hzero : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (tensorLocalChartConvolution C mu K ell u i) x := by
    apply hc.congr_of_eventuallyEq
    filter_upwards [(C.chart i).open_source.mem_nhds (C.inner_subset i hi)] with z hz
    exact Set.indicator_of_mem hz _
  have heq : (fun z => chi i z ^ 2 • tensorLocalChartConvolution C mu K ell u i z) =
      (chi i * chi i) • tensorLocalChartConvolution C mu K ell u i := by
    funext z
    change chi i z ^ 2 • tensorLocalChartConvolution C mu K ell u i z =
      (chi i z * chi i z) • tensorLocalChartConvolution C mu K ell u i z
    rw [pow_two]
  rw [heq]
  exact ((hchi i).contMDiffAt.mul (hchi i).contMDiffAt).smul hzero

end
end GlobalEmbedding.Offline
