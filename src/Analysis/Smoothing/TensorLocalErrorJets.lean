import Smoothing.TensorLocalParameter

/-!
# Actual local tensor error jets with finite overlap

The square partition is required only as a germ at the evaluation point.
The genuine convolution errors, both frame factors, the chart transition,
and every cutoff derivative are retained. The uniform transfer constant uses
the active overlap degree, never the total cardinality of the local family.
This is the local-to-global derivative step, not an assumed final tail bound.
-/

open Module MeasureTheory Manifold IsManifold GlobalEmbedding.Paper Function Set Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Offline
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι X E : Type*} [Fintype ι] [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]
  {n : ℕ} {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]

def tensorLocalConvolutionError (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (u : X → Fin (n*n) → ℝ) (i : ι) : E → Fin (n*n) → ℝ :=
  tensorLocalConvolution C mu K ell u i - tensorLocalCoordinateExtension C u i

def tensorLocalErrorEntry (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → X → ℝ)
    (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x))
    (p i : ι) (a d r s : Fin n) (y : E) : ℝ :=
  chi i ((C.chart p).symm y) ^ 2 *
    (tensorLocalFrameTransition C b p i a r y * tensorLocalFrameTransition C b p i d s y) *
    tensorLocalConvolutionError C mu K ell (tensorLocalFieldCoefficients b H i) i
      (C.chart i ((C.chart p).symm y)) (finProdFinEquiv (r,s))

def tensorLocalErrorCoordinates (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → X → ℝ)
    (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x)) (p : ι) (y : E) : Fin (n*n) → ℝ :=
  tensorFrameComponents (b p ((C.chart p).symm y))
    (tensorLocalFieldSmoothing C mu K ell chi b H ((C.chart p).symm y) - H ((C.chart p).symm y))

theorem tensorLocalTransition_contDiffOn (C : TensorBufferedChartFamily ι X E)
    (hchart : ∀ i, C.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ X) (p i : ι) :
    ContDiffOn ℝ ∞ (C.chart i ∘ (C.chart p).symm) (tensorLocalChartOverlap C p i) :=
  ((contMDiffOn_of_mem_maximalAtlas (hchart i)).comp
    ((contMDiffOn_symm_of_mem_maximalAtlas (hchart p)).mono (fun _ h => h.1))
    (fun _ h => C.inner_subset i h.2)).contDiffOn

theorem tensorLocalConvolutionError_contDiffOn
    (C : TensorBufferedChartFamily ι X E) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ C.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (u : X → Fin (n*n) → ℝ) (i : ι)
    (hu : ContDiffOn ℝ ∞ (u ∘ (C.chart i).symm) (C.chart i).target) :
    ContDiffOn ℝ ∞ (tensorLocalConvolutionError C mu K ell u i) (tensorLocalInner C i) :=
  (tensorLocalConvolution_contDiffOn C mu hK hcompact hsupp hrho hell hell1 u i hu).sub
    ((tensorLocalCoordinateExtension_contDiffOn C u i hu).mono (fun _ hz => hz.1))

theorem tensorLocalErrorEntry_contDiffOn
    (C : TensorBufferedChartFamily ι X E)
    (hchart : ∀ i, C.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ X)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ C.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : ι → X → ℝ) (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x)) (p i : ι)
    (hH : ContDiffOn ℝ ∞ (tensorLocalFieldCoefficients b H i ∘ (C.chart i).symm) (C.chart i).target)
    (hframe : ∀ a r, ContDiffOn ℝ ∞ (tensorLocalFrameTransition C b p i a r)
      (tensorLocalChartOverlap C p i)) (a d r s : Fin n) :
    ContDiffOn ℝ ∞ (tensorLocalErrorEntry C mu K ell chi b H p i a d r s)
      (tensorLocalChartOverlap C p i) := by
  have hw : ContDiffOn ℝ ∞ (chi i ∘ (C.chart p).symm) (tensorLocalChartOverlap C p i) :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hchart p))).contDiffOn.mono
      (fun _ hz => hz.1)
  have he := tensorLocalConvolutionError_contDiffOn C mu hK hcompact hsupp hrho hell hell1
    (tensorLocalFieldCoefficients b H i) i hH
  exact ((hw.pow 2).mul ((hframe a r).mul (hframe d s))).mul
    (((contDiffOn_pi.mp he) (finProdFinEquiv (r,s))).comp
      (tensorLocalTransition_contDiffOn C hchart p i)
      (fun _ hz => tensorLocalInner_mem C i hz.2))

theorem tensorLocalErrorEntry_eventuallyEq_zero
    (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → X → ℝ)
    (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x)) (p i : ι)
    (a d r s : Fin n) {y : E} (hy : y ∈ (C.chart p).target)
    (hi : (C.chart p).symm y ∉ tsupport (chi i)) :
    tensorLocalErrorEntry C mu K ell chi b H p i a d r s =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
  filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hi).comp_tendsto
    ((C.chart p).symm.continuousAt hy)] with z hz
  change chi i ((C.chart p).symm z) = 0 at hz
  simp only [tensorLocalErrorEntry, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]

/-- The actual tensor error has full J-transpose/error/J coordinates at
every point where the genuine square partition holds. -/
theorem tensorLocalErrorCoordinates_entry_at
    (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → X → ℝ)
    (hsupport : ∀ i, tsupport (chi i) ⊆ C.inner i)
    (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x)) (p : ι) (a d : Fin n) (y : E)
    (hpartition : ∑ i, chi i ((C.chart p).symm y)^2 = 1) :
    tensorLocalErrorCoordinates C mu K ell chi b H p y (finProdFinEquiv (a,d)) =
      ∑ i, ∑ r, ∑ s, tensorLocalErrorEntry C mu K ell chi b H p i a d r s y := by
  unfold tensorLocalErrorCoordinates
  rw [tensorLocalFieldSmoothing_error_at C mu K ell chi hsupport b H _ hpartition]
  simp only [tensorFrameComponents, Equiv.symm_apply_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensorFromFrameComponents, Matrix.toBilin_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold tensorLocalErrorEntry tensorLocalFrameTransition tensorLocalConvolutionError
  simp only [Pi.sub_apply]
  ring

/-- A local partition suffices as a germ, so every genuine derivative can
use the transported local-error sum. -/
theorem tensorLocalErrorCoordinates_entry_eventuallyEq
    (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → X → ℝ)
    (hsupport : ∀ i, tsupport (chi i) ⊆ C.inner i)
    (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x)) (p : ι) (a d : Fin n) {y : E}
    (hpartition : ∀ᶠ z in 𝓝 y, ∑ i, chi i ((C.chart p).symm z)^2 = 1) :
    (fun z => tensorLocalErrorCoordinates C mu K ell chi b H p z (finProdFinEquiv (a,d))) =ᶠ[𝓝 y]
      (fun z => ∑ i, ∑ r, ∑ s, tensorLocalErrorEntry C mu K ell chi b H p i a d r s z) := by
  filter_upwards [hpartition] with z hz
  exact tensorLocalErrorCoordinates_entry_at C mu K ell chi hsupport b H p a d z hz

theorem tensorLocalErrorEntry_jet_le
    (C : TensorBufferedChartFamily ι X E)
    (hchart : ∀ i, C.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ X)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ C.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : ι → X → ℝ) (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (b : ι → (x : X) → Basis (Fin n) ℝ (V x))
    (H : (x : X) → LinearMap.BilinForm ℝ (V x)) (p i : ι)
    (hH : ContDiffOn ℝ ∞ (tensorLocalFieldCoefficients b H i ∘ (C.chart i).symm) (C.chart i).target)
    (hframe : ∀ a r, ContDiffOn ℝ ∞ (tensorLocalFrameTransition C b p i a r)
      (tensorLocalChartOverlap C p i))
    (B T J : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) (hT : ∀ k, 0 ≤ T k) (hJ : ∀ k, 0 ≤ J k)
    {y : E} (hy : y ∈ tensorLocalChartOverlap C p i) (j : ℕ) (R : ℝ)
    (hweight : ∀ k, ‖iteratedFDeriv ℝ k (chi i ∘ (C.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ k (C.chart i ∘ (C.chart p).symm) y‖ ≤ T k)
    (hframeBound : ∀ a r k, ‖iteratedFDeriv ℝ k (tensorLocalFrameTransition C b p i a r) y‖ ≤ J k)
    (hlocal : ∀ k ≤ j, ‖iteratedFDeriv ℝ k
      (tensorLocalConvolutionError C mu K ell (tensorLocalFieldCoefficients b H i) i)
      (C.chart i ((C.chart p).symm y))‖ ≤ R) (a d r s : Fin n) :
    ‖iteratedFDeriv ℝ j (tensorLocalErrorEntry C mu K ell chi b H p i a d r s) y‖ ≤
      tensorTransferCore B T J j * R := by
  have hw : ContDiffOn ℝ ∞ (chi i ∘ (C.chart p).symm) (tensorLocalChartOverlap C p i) :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hchart p))).contDiffOn.mono
      (fun _ hz => hz.1)
  have he := tensorLocalConvolutionError_contDiffOn C mu hK hcompact hsupp hrho hell hell1
    (tensorLocalFieldCoefficients b H i) i hH
  have hg := (contDiffOn_pi.mp he) (finProdFinEquiv (r,s))
  have hyi := tensorLocalInner_mem C i hy.2
  exact tensor_transferred_entry_jet_le B T J hB hT hJ
    (tensorLocalChartOverlap_open C p i) (tensorLocalInner_open C i)
    hw (hframe a r) (hframe d s) hg (tensorLocalTransition_contDiffOn C hchart p i)
    (fun _ hz => tensorLocalInner_mem C i hz.2) hy j R hweight (hframeBound a r) (hframeBound d s)
    htransition (fun k hk => (tensor_component_jet_le
      (he.contDiffAt ((tensorLocalInner_open C i).mem_nhds hyi)) _ k).trans (hlocal k hk))

/-- The real error's every derivative uses only active overlap and local
convolution errors. Partition is local, and no global parameter atlas exists
in this statement. The two native frame factors remain explicit. -/
theorem tensorLocalErrorCoordinates_jet_le
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
      (tensorLocalChartOverlap C p i))
    (B T J : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) (hT : ∀ k, 0 ≤ T k) (hJ : ∀ k, 0 ≤ J k)
    (D : ℕ) (p : ι) {y : E} (hy : y ∈ (C.chart p).target)
    (hpartition : ∀ᶠ z in 𝓝 y, ∑ i, chi i ((C.chart p).symm z)^2 = 1)
    (hD : (activeCutoffIndices chi ((C.chart p).symm y)).card ≤ D)
    (m j : ℕ) (hjm : j ≤ m) (R : ℝ) (hR : 0 ≤ R)
    (hweight : ∀ i, (C.chart p).symm y ∈ tsupport (chi i) →
      ∀ k, ‖iteratedFDeriv ℝ k (chi i ∘ (C.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ i, (C.chart p).symm y ∈ tsupport (chi i) →
      ∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k (C.chart i ∘ (C.chart p).symm) y‖ ≤ T k)
    (hframeBound : ∀ i, (C.chart p).symm y ∈ tsupport (chi i) →
      ∀ a r k, ‖iteratedFDeriv ℝ k (tensorLocalFrameTransition C b p i a r) y‖ ≤ J k)
    (hlocal : ∀ i, (C.chart p).symm y ∈ tsupport (chi i) →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k
        (tensorLocalConvolutionError C mu K ell (tensorLocalFieldCoefficients b H i) i)
        (C.chart i ((C.chart p).symm y))‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (tensorLocalErrorCoordinates C mu K ell chi b H p) y‖ ≤
      tensorTransferConstant n B T J D m * R := by
  classical
  have houtput := tensorLocalFieldSmoothing_coordinates_contDiffOn C hchart mu hK hcompact
    hsupp hrho hell hell1 chi hchi hsupport b H hH hframe p
  have he : ContDiffOn ℝ ∞ (tensorLocalErrorCoordinates C mu K ell chi b H p) (C.chart p).target :=
    houtput.sub (hH p)
  apply tensor_jet_le_of_components (he.contDiffAt ((C.chart p).open_target.mem_nhds hy)) j _
    (mul_nonneg (tensorTransferConstant_nonneg n hB hT hJ D m) hR)
  intro k
  obtain ⟨⟨a,d⟩,rfl⟩ := finProdFinEquiv.surjective k
  rw [((tensorLocalErrorCoordinates_entry_eventuallyEq C mu K ell chi hsupport b H p a d
    hpartition).iteratedFDeriv ℝ j).eq_of_nhds]
  let S := activeCutoffIndices chi ((C.chart p).symm y)
  have hreg (i : ι) (r s : Fin n) :
      ContDiffAt ℝ ∞ (tensorLocalErrorEntry C mu K ell chi b H p i a d r s) y := by
    by_cases hi : (C.chart p).symm y ∈ tsupport (chi i)
    · exact (tensorLocalErrorEntry_contDiffOn C hchart mu hK hcompact hsupp hrho hell hell1
        chi hchi b H p i (hH i) (hframe p i) a d r s).contDiffAt
        ((tensorLocalChartOverlap_open C p i).mem_nhds ⟨hy, hsupport i hi⟩)
    · exact contDiffAt_const.congr_of_eventuallyEq
        (tensorLocalErrorEntry_eventuallyEq_zero C mu K ell chi b H p i a d r s hy hi)
  have hsum := tensor_finite_entry_sum_jet_le
    (fun i r s => tensorLocalErrorEntry C mu K ell chi b H p i a d r s)
    S D hD y j (tensorTransferCore B T J j * R)
    (mul_nonneg (tensorTransferCore_nonneg hB hT hJ j) hR) hreg
    (fun i hi r s => tensorLocalErrorEntry_eventuallyEq_zero C mu K ell chi b H p i a d r s hy
      (by simpa [S] using hi))
    (fun i hi r s => by
      have hi' : (C.chart p).symm y ∈ tsupport (chi i) := by simpa [S] using hi
      exact tensorLocalErrorEntry_jet_le C hchart mu hK hcompact hsupp hrho hell hell1
        chi hchi b H p i (hH i) (hframe p i) B T J hB hT hJ ⟨hy,hsupport i hi'⟩ j R
        (hweight i hi') (htransition i hi') (hframeBound i hi')
        (fun k hk => hlocal i hi' k (hk.trans hjm)) a d r s)
  apply hsum.trans
  unfold tensorTransferConstant
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ hR
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  exact Finset.single_le_sum (fun k _ => tensorTransferCore_nonneg hB hT hJ k)
    (by simpa using hjm)

#print axioms tensorLocalErrorCoordinates_jet_le
#print axioms tensorLocalErrorCoordinates_entry_eventuallyEq

end
end GlobalEmbedding.Offline
