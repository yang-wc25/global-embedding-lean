import Smoothing.TensorSmoothingRegularity

/-!
# Global derivatives of the same buffered tensor error

The output is an actual field of bilinear forms. Its original chart
coefficients are differentiated, including the two frame-change factors.
Finite overlap, not the number of charts, controls the global sum.
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

/-- The coordinates of the SAME actual bilinear error in every source frame. -/
def bufferedTensorErrorCoordinates (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (p : Fin A.count) (y : E) :
    Fin (n * n) → ℝ :=
  tensorFrameComponents (b p ((A.chart p).symm y))
    (bufferedTensorSmoothing A mu K ell chi b H ((A.chart p).symm y) - H ((A.chart p).symm y))

theorem tensorErrorEntry_jet_le (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
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
      (bufferedChartOverlap A p i))
    (B T J : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) (hT : ∀ k, 0 ≤ T k) (hJ : ∀ k, 0 ≤ J k)
    {y : E} (hy : y ∈ bufferedChartOverlap A p i) (j : ℕ) (R : ℝ)
    (hweight : ∀ k, ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ k, 1 ≤ k →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hframeBound : ∀ a r k, ‖iteratedFDeriv ℝ k (tensorFrameTransition A b p i a r) y‖ ≤ J k)
    (hlocal : ∀ k ≤ j, ‖iteratedFDeriv ℝ k
      (bufferedLocalError A mu K ell (tensorCoefficientField A b H i) i)
      (A.chart i ((A.chart p).symm y))‖ ≤ R) (a d r s : Fin n) :
    ‖iteratedFDeriv ℝ j (tensorErrorEntry A mu K ell chi b H p i a d r s) y‖ ≤
      tensorTransferCore B T J j * R := by
  have hw : ContDiffOn ℝ ∞ (chi i ∘ (A.chart p).symm) (bufferedChartOverlap A p i) :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem p))).contDiffOn.mono
      (fun _ hz => hz.1)
  have he := tensorLocalError_contDiffOn A mu hK hcompact hsupp hrho hell hell1 b H i hH
  have hg := (contDiffOn_pi.mp he) (finProdFinEquiv (r, s))
  have hyi := bufferedTransition_maps A p i hy
  exact tensor_transferred_entry_jet_le B T J hB hT hJ
    (bufferedChartOverlap_open A p i) (bufferedInnerCoordinates_open A i)
    hw (hframe a r) (hframe d s) hg (bufferedTransition_contDiffOn A hA p i)
    (bufferedTransition_maps A p i) hy j R hweight (hframeBound a r) (hframeBound d s)
    htransition (fun k hk => (tensor_component_jet_le
      (he.contDiffAt ((bufferedInnerCoordinates_open A i).mem_nhds hyi)) _ k).trans (hlocal k hk))

/-- Every global entry is genuinely smooth at each receiving-chart point.
Inactive terms use their actual zero germs. -/
theorem tensorErrorEntry_contDiffAt (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x)) (p i : Fin A.count)
    (hH : ContDiffOn ℝ ∞ (tensorCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target)
    (hframe : ∀ a r, ContDiffOn ℝ ∞ (tensorFrameTransition A b p i a r)
      (bufferedChartOverlap A p i)) (a d r s : Fin n)
    {y : E} (hy : y ∈ (A.chart p).target) :
    ContDiffAt ℝ ∞ (tensorErrorEntry A mu K ell chi b H p i a d r s) y := by
  by_cases hi : (A.chart p).symm y ∈ tsupport (chi i)
  · exact (tensorErrorEntry_contDiffOn A hA mu hK hcompact hsupp hrho hell hell1
      chi hchi b H p i hH hframe a d r s).contDiffAt
      ((bufferedChartOverlap_open A p i).mem_nhds ⟨hy, hchiSupport i hi⟩)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (tensorErrorEntry_eventuallyEq_zero A mu K ell chi b H p i a d r s hy hi)

/-- The same actual tensor error has smooth original coefficient functions. -/
theorem bufferedTensorErrorCoordinates_contDiffOn
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (tensorCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target)
    (hframe : ∀ p i a r, ContDiffOn ℝ ∞ (tensorFrameTransition A b p i a r)
      (bufferedChartOverlap A p i)) (p : Fin A.count) :
    ContDiffOn ℝ ∞ (bufferedTensorErrorCoordinates A mu K ell chi b H p) (A.chart p).target := by
  apply contDiffOn_pi.mpr
  intro k y hy
  obtain ⟨⟨a, d⟩, rfl⟩ := finProdFinEquiv.surjective k
  change ContDiffWithinAt ℝ ∞ (fun z => tensorFrameComponents _ _ (finProdFinEquiv (a, d))) _ _
  rw [bufferedTensorSmoothing_error_chart_eq A mu K ell chi hchiSupport hpartition b H p a d]
  apply ContDiffAt.contDiffWithinAt
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun r _ => ContDiffAt.sum fun s _ =>
    tensorErrorEntry_contDiffAt A hA mu hK hcompact hsupp hrho hell hell1 chi hchi hchiSupport
      b H p i (hH i) (hframe p i) a d r s hy

/-- All native jets of the SAME global tensor error are bounded by genuine
local convolution errors. The explicit constant contains both frame factors
and the active overlap multiplicity, but no total chart count. -/
theorem bufferedTensorErrorCoordinates_jet_le
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (tensorCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target)
    (hframe : ∀ p i a r, ContDiffOn ℝ ∞ (tensorFrameTransition A b p i a r)
      (bufferedChartOverlap A p i))
    (B T J : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) (hT : ∀ k, 0 ≤ T k) (hJ : ∀ k, 0 ≤ J k)
    (D : ℕ) (p : Fin A.count) {y : E} (hy : y ∈ (A.chart p).target)
    (hD : (activeCutoffIndices chi ((A.chart p).symm y)).card ≤ D)
    (m j : ℕ) (hjm : j ≤ m) (R : ℝ) (hR : 0 ≤ R)
    (hweight : ∀ i, (A.chart p).symm y ∈ tsupport (chi i) →
      ∀ k, ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ i, (A.chart p).symm y ∈ tsupport (chi i) →
      ∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hframeBound : ∀ i, (A.chart p).symm y ∈ tsupport (chi i) →
      ∀ a r k, ‖iteratedFDeriv ℝ k (tensorFrameTransition A b p i a r) y‖ ≤ J k)
    (hlocal : ∀ i, (A.chart p).symm y ∈ tsupport (chi i) →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k
        (bufferedLocalError A mu K ell (tensorCoefficientField A b H i) i)
        (A.chart i ((A.chart p).symm y))‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (bufferedTensorErrorCoordinates A mu K ell chi b H p) y‖ ≤
      tensorTransferConstant n B T J D m * R := by
  classical
  have he := bufferedTensorErrorCoordinates_contDiffOn A hA mu hK hcompact hsupp hrho hell hell1
    chi hchi hchiSupport hpartition b H hH hframe p
  apply tensor_jet_le_of_components (he.contDiffAt ((A.chart p).open_target.mem_nhds hy)) j _
    (mul_nonneg (tensorTransferConstant_nonneg n hB hT hJ D m) hR)
  intro k
  obtain ⟨⟨a, d⟩, rfl⟩ := finProdFinEquiv.surjective k
  change ‖iteratedFDeriv ℝ j (fun z => tensorFrameComponents _ _ (finProdFinEquiv (a, d))) y‖ ≤ _
  rw [bufferedTensorSmoothing_error_chart_eq A mu K ell chi hchiSupport hpartition b H p a d]
  let S := activeCutoffIndices chi ((A.chart p).symm y)
  have hsum := tensor_finite_entry_sum_jet_le
    (fun i r s => tensorErrorEntry A mu K ell chi b H p i a d r s)
    S D hD y j (tensorTransferCore B T J j * R)
    (mul_nonneg (tensorTransferCore_nonneg hB hT hJ j) hR)
    (fun i r s => tensorErrorEntry_contDiffAt A hA mu hK hcompact hsupp hrho hell hell1
      chi hchi hchiSupport b H p i (hH i) (hframe p i) a d r s hy)
    (fun i hi r s => tensorErrorEntry_eventuallyEq_zero A mu K ell chi b H p i a d r s hy
      (by simpa [S] using hi))
    (fun i hi r s => by
      have hi' : (A.chart p).symm y ∈ tsupport (chi i) := by simpa [S] using hi
      exact tensorErrorEntry_jet_le A hA mu hK hcompact hsupp hrho hell hell1 chi hchi b H p i
        (hH i) (hframe p i) B T J hB hT hJ ⟨hy, hchiSupport i hi'⟩ j R
        (hweight i hi') (htransition i hi') (hframeBound i hi')
        (fun l hl => hlocal i hi' l (hl.trans hjm)) a d r s)
  apply hsum.trans
  unfold tensorTransferConstant
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ hR
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  exact Finset.single_le_sum (fun l _ => tensorTransferCore_nonneg hB hT hJ l)
    (by simpa using hjm)

end

end GlobalEmbedding.Offline
