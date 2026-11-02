import Smoothing.TensorGainJets

/-!
# The actual tensor smoother is a linear operator

All addition identities use integrability on the real sampling region of
an active cutoff, proved from local tensor coefficients and the compact
signed kernel. The operator acts on genuine fields of bilinear forms whose
original chart coefficients are smooth. It preserves that same space.
-/

open Module MeasureTheory GlobalEmbedding.Paper Function Set Manifold
open scoped BigOperators ContDiff Topology

namespace GlobalEmbedding.Offline

noncomputable section

set_option backward.isDefEq.respectTransparency false

section Algebra

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]

@[simp] theorem tensorFrameComponents_add (b : Basis (Fin n) ℝ V)
    (H L : LinearMap.BilinForm ℝ V) :
    tensorFrameComponents b (H + L) = tensorFrameComponents b H + tensorFrameComponents b L := rfl

@[simp] theorem tensorFrameComponents_smul (b : Basis (Fin n) ℝ V)
    (c : ℝ) (H : LinearMap.BilinForm ℝ V) :
    tensorFrameComponents b (c • H) = c • tensorFrameComponents b H := rfl

@[simp] theorem tensorFromFrameComponents_add (b : Basis (Fin n) ℝ V)
    (u v : Fin (n * n) → ℝ) :
    tensorFromFrameComponents b (u + v) = tensorFromFrameComponents b u + tensorFromFrameComponents b v := by
  unfold tensorFromFrameComponents
  exact map_add (Matrix.toBilin b) _ _

end Algebra

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {n : ℕ} {V : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]

/-- Compact kernel support and the original buffer give actual integrability;
no global integrability of the zero-extended coefficient field is assumed. -/
theorem tensorLocalSmoothing_integrable (A : BufferedAtlas M E)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (i : Fin A.count)
    (hH : ContDiffOn ℝ ∞ (tensorCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target)
    {z : E} (hz : z ∈ bufferedInnerCoordinates A i) :
    Integrable (fun y => K y •
      bufferedCoordinateExtension A (tensorCoefficientField A b H i) i (z - ell • y)) mu := by
  have hcont : ContinuousOn (fun y =>
      bufferedCoordinateExtension A (tensorCoefficientField A b H i) i (z - ell • y)) (tsupport K) := by
    apply (tensorCoordinateExtension_contDiffOn A b H i hH).continuousOn.comp
      (continuous_const.sub (continuous_const.smul continuous_id)).continuousOn
    intro y hy
    change z - ell • y ∈ (A.chart i).target
    simpa only [one_smul] using buffered_kernel_segment A i hsupp hrho hell hell1 hz hy
      (s := 1) (by simp)
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_smul_subset_left _ _).trans (subset_tsupport K))).mp
    ((hK.continuous.continuousOn.smul hcont).integrableOn_compact hcompact)

/-- Addition is preserved by the actual global integral/reconstruction. -/
theorem bufferedTensorSmoothing_add (A : BufferedAtlas M E)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ) (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H L : (x : M) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (tensorCoefficientField A b H i ∘ (A.chart i).symm) (A.chart i).target)
    (hL : ∀ i, ContDiffOn ℝ ∞ (tensorCoefficientField A b L i ∘ (A.chart i).symm) (A.chart i).target) :
    bufferedTensorSmoothing A mu K ell chi b (H + L) =
      bufferedTensorSmoothing A mu K ell chi b H + bufferedTensorSmoothing A mu K ell chi b L := by
  funext x
  change (∑ i, chi i x ^ 2 • tensorFromFrameComponents (b i x)
      (bufferedChartSmoothing A mu K ell (tensorCoefficientField A b (H + L) i) i x)) =
    (∑ i, chi i x ^ 2 • tensorFromFrameComponents (b i x)
      (bufferedChartSmoothing A mu K ell (tensorCoefficientField A b H i) i x)) +
    (∑ i, chi i x ^ 2 • tensorFromFrameComponents (b i x)
      (bufferedChartSmoothing A mu K ell (tensorCoefficientField A b L i) i x))
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : chi i x = 0
  · simp only [hi, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_smul, add_zero]
  · have hx := hchiSupport i (subset_tsupport (chi i) hi)
    have hxS := A.inner_subset i hx
    have hz := bufferedInnerCoordinates_mem A i hx
    have hIH := tensorLocalSmoothing_integrable A mu hK hcompact hsupp hrho hell hell1 b H i (hH i) hz
    have hIL := tensorLocalSmoothing_integrable A mu hK hcompact hsupp hrho hell hell1 b L i (hL i) hz
    have hext : bufferedCoordinateExtension A (tensorCoefficientField A b (H + L) i) i =
        bufferedCoordinateExtension A (tensorCoefficientField A b H i) i +
        bufferedCoordinateExtension A (tensorCoefficientField A b L i) i := by
      funext y
      by_cases hy : y ∈ (A.chart i).target
      · simp only [bufferedCoordinateExtension, Set.indicator_of_mem hy,
          Function.comp_apply, tensorCoefficientField, Pi.add_apply, tensorFrameComponents_add]
      · simp only [bufferedCoordinateExtension, Set.indicator_of_notMem hy, Pi.add_apply, add_zero]
    have hlocal : bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b (H + L) i) i (A.chart i x) =
        bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b H i) i (A.chart i x) +
        bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b L i) i (A.chart i x) := by
      change (∫ y, K y • bufferedCoordinateExtension A (tensorCoefficientField A b (H + L) i) i
        (A.chart i x - ell • y) ∂mu) = _
      rw [hext]
      simp only [Pi.add_apply, smul_add]
      exact integral_add hIH hIL
    simp only [bufferedChartSmoothing, Set.indicator_of_mem hxS, Function.comp_apply,
      hlocal, tensorFromFrameComponents_add, smul_add]

/-- The scalar commutes with the true signed integral and both indicators. -/
theorem bufferedTensorSmoothing_smul (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (c : ℝ) :
    bufferedTensorSmoothing A mu K ell chi b (c • H) = c • bufferedTensorSmoothing A mu K ell chi b H := by
  have hext (i : Fin A.count) : bufferedCoordinateExtension A (tensorCoefficientField A b (c • H) i) i =
      c • bufferedCoordinateExtension A (tensorCoefficientField A b H i) i := by
    funext y
    by_cases hy : y ∈ (A.chart i).target
    · simp only [bufferedCoordinateExtension, Set.indicator_of_mem hy, Function.comp_apply,
        tensorCoefficientField, Pi.smul_apply, tensorFrameComponents_smul]
    · simp only [bufferedCoordinateExtension, Set.indicator_of_notMem hy, Pi.smul_apply, smul_zero]
  have hlocal (i : Fin A.count) (z : E) :
      bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b (c • H) i) i z =
        c • bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b H i) i z := by
    change (∫ y, K y • bufferedCoordinateExtension A (tensorCoefficientField A b (c • H) i) i
      (z - ell • y) ∂mu) = _
    rw [hext]
    simp only [Pi.smul_apply, smul_comm (K _) c]
    exact integral_smul c _
  funext x
  change (∑ i, chi i x ^ 2 • tensorFromFrameComponents (b i x)
      (bufferedChartSmoothing A mu K ell (tensorCoefficientField A b (c • H) i) i x)) =
    c • ∑ i, chi i x ^ 2 • tensorFromFrameComponents (b i x)
      (bufferedChartSmoothing A mu K ell (tensorCoefficientField A b H i) i x)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ (A.chart i).source
  · simp only [bufferedChartSmoothing, Set.indicator_of_mem hx, Function.comp_apply,
      hlocal, tensorFromFrameComponents_smul, smul_comm (chi i x ^ 2) c]
  · simp only [bufferedChartSmoothing, Set.indicator_of_notMem hx]
    have hz : tensorFromFrameComponents (b i x) 0 = 0 := by
      unfold tensorFromFrameComponents
      exact map_zero (Matrix.toBilin (b i x))
    rw [hz, smul_zero, smul_zero]

/-- Genuine tensor fields with smooth original chart coefficients form a
linear subspace of actual dependent bilinear fields. -/
def smoothBufferedTensorFields (A : BufferedAtlas M E)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x)) :
    Submodule ℝ ((x : M) → LinearMap.BilinForm ℝ (V x)) where
  carrier H := ∀ i, ContDiffOn ℝ ∞ (tensorCoefficientField A b H i ∘ (A.chart i).symm) (A.chart i).target
  zero_mem' := by
    intro i
    change ContDiffOn ℝ ∞ (fun _ : E => (0 : Fin (n * n) → ℝ)) (A.chart i).target
    exact contDiffOn_const
  add_mem' := by
    intro H L hH hL i
    exact (hH i).add (hL i)
  smul_mem' := by
    intro c H hH i
    exact (hH i).const_smul c

/-- One actual linear tensor smoothing on the original coefficient-smooth
space. Its output smoothness is proved, not supplied as a hypothesis. -/
def bufferedTensorSmoothingLinearMap (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (hframe : ∀ p i a r, ContDiffOn ℝ ∞ (tensorFrameTransition A b p i a r)
      (bufferedChartOverlap A p i)) :
    smoothBufferedTensorFields A b →ₗ[ℝ] smoothBufferedTensorFields A b where
  toFun H := ⟨bufferedTensorSmoothing A mu K ell chi b H,
    bufferedTensorSmoothingCoordinates_contDiffOn A hA mu hK hcompact hsupp hrho hell hell1
      chi hchi hchiSupport b H H.property hframe⟩
  map_add' H L := by
    apply Subtype.ext
    exact bufferedTensorSmoothing_add A mu hK hcompact hsupp hrho hell hell1 chi hchiSupport
      b H L H.property L.property
  map_smul' c H := by
    apply Subtype.ext
    exact bufferedTensorSmoothing_smul A mu K ell chi b H c

end

end GlobalEmbedding.Offline
