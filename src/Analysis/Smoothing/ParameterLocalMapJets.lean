import Smoothing.ParameterLocalMap
import GlobalEmbedding.Offline.BufferedSmoothingJets

/-!
# All genuine local-map error derivatives with no global chart cover

This is the same actual integral and finite cutoff sum. Only a germ of the
square partition at the evaluation point is used. Active support degree,
actual cutoff jets and true coordinate transition jets control all orders;
the constant is the original bufferedTransferConstant and contains no total
chart count. Coordinate smoothness is needed only on each real chart target.
-/

open GlobalEmbedding.Offline MeasureTheory GlobalEmbedding.Paper Function Filter Set Manifold IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

section BufferedJets

variable {ι E F M : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual local error used in the global identity. -/
def parameterLocalMapError (A : TensorBufferedChartFamily ι M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (u : M → F) (i : ι) : E → F :=
  tensorLocalConvolution A mu K ell u i - tensorLocalCoordinateExtension A u i

/-- A receiving chart's genuine overlap with an original inner domain. -/
def parameterLocalMapOverlap (A : TensorBufferedChartFamily ι M E) (p i : ι) : Set E :=
  (A.chart p).target ∩ (A.chart p).symm ⁻¹' A.inner i

/-- One genuine summand of the global error in the receiving chart. -/
def parameterLocalMapErrorPullback (A : TensorBufferedChartFamily ι M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → M → ℝ) (u : M → F)
    (p i : ι) : E → F :=
  fun y => chi i ((A.chart p).symm y) ^ 2 •
    parameterLocalMapError A mu K ell u i (A.chart i ((A.chart p).symm y))

theorem parameterLocalMapOverlap_open (A : TensorBufferedChartFamily ι M E) (p i : ι) :
    IsOpen (parameterLocalMapOverlap A p i) :=
  (A.chart p).isOpen_inter_preimage_symm (A.inner_open i)

theorem parameterLocalMapTransition_maps (A : TensorBufferedChartFamily ι M E) (p i : ι) :
    MapsTo (A.chart i ∘ (A.chart p).symm) (parameterLocalMapOverlap A p i)
      (tensorLocalInner A i) :=
  fun _ hy => tensorLocalInner_mem A i hy.2

theorem parameterLocalMapTransition_contDiffOn (A : TensorBufferedChartFamily ι M E)
    (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (p i : ι) :
    ContDiffOn ℝ ∞ (A.chart i ∘ (A.chart p).symm) (parameterLocalMapOverlap A p i) := by
  exact ((contMDiffOn_of_mem_maximalAtlas (hA i)).comp
    ((contMDiffOn_symm_of_mem_maximalAtlas (hA p)).mono (fun _ hy => hy.1))
      (fun _ hy => A.inner_subset i hy.2)).contDiffOn

theorem parameterLocalMapError_contDiffOn (A : TensorBufferedChartFamily ι M E)
    (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    {u : M → F} (hu : ∀ i, ContDiffOn ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i).target) (i : ι) :
    ContDiffOn ℝ ∞ (parameterLocalMapError A mu K ell u i) (tensorLocalInner A i) :=
  (tensorLocalConvolution_contDiffOn A mu hK hcompact hsupp hrho hell hell1 u i (hu i)).sub
    ((tensorLocalCoordinateExtension_contDiffOn A u i (hu i)).mono (fun _ hy => hy.1))

/-- Native regularity on each actual active overlap. -/
theorem parameterLocalMapErrorPullback_contDiffOn (A : TensorBufferedChartFamily ι M E)
    (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : ι → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    {u : M → F} (hu : ∀ i, ContDiffOn ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i).target) (p i : ι) :
    ContDiffOn ℝ ∞ (parameterLocalMapErrorPullback A mu K ell chi u p i) (parameterLocalMapOverlap A p i) := by
  have hweight : ContDiffOn ℝ ∞ (chi i ∘ (A.chart p).symm) (parameterLocalMapOverlap A p i) :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA p))).contDiffOn.mono
      (fun _ hy => hy.1)
  exact (hweight.pow 2).smul ((parameterLocalMapError_contDiffOn A hA mu hK hcompact hsupp hrho
    hell hell1 hu i).comp (parameterLocalMapTransition_contDiffOn A hA p i) (parameterLocalMapTransition_maps A p i))

/-- Off an actual cutoff support, every error summand has a genuine zero germ. -/
theorem parameterLocalMapErrorPullback_eventuallyEq_zero (A : TensorBufferedChartFamily ι M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → M → ℝ) (u : M → F)
    (p i : ι) {y : E} (hy : y ∈ (A.chart p).target)
    (hi : (A.chart p).symm y ∉ tsupport (chi i)) :
    parameterLocalMapErrorPullback A mu K ell chi u p i =ᶠ[𝓝 y] (fun _ => (0 : F)) := by
  filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hi).comp_tendsto
    ((A.chart p).symm.continuousAt hy)] with z hz
  change chi i ((A.chart p).symm z) = 0 at hz
  simp only [parameterLocalMapErrorPullback, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_smul]

/-- The actual cutoff and transition derivative providers control one active
summand by an explicit constant times the actual local error-jet bound. -/
theorem parameterLocalMapErrorPullback_jet_le (A : TensorBufferedChartFamily ι M E)
    (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : ι → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    {u : M → F} (hu : ∀ i, ContDiffOn ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i).target)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j)
    (p i : ι) {y : E} (hy : y ∈ parameterLocalMapOverlap A p i)
    (j : ℕ) (R : ℝ) (_hR : 0 ≤ R)
    (hweight : ∀ k, ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hlocal : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (parameterLocalMapError A mu K ell u i)
      (A.chart i ((A.chart p).symm y))‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (parameterLocalMapErrorPullback A mu K ell chi u p i) y‖ ≤
      bufferedTransferCore B T j * R := by
  let O := parameterLocalMapOverlap A p i
  let w := chi i ∘ (A.chart p).symm
  let v := parameterLocalMapError A mu K ell u i ∘ (A.chart i ∘ (A.chart p).symm)
  have hO : IsOpen O := parameterLocalMapOverlap_open A p i
  have hw : ContDiffOn ℝ ∞ w O :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA p))).contDiffOn.mono
      (fun _ hz => hz.1)
  have hg := parameterLocalMapError_contDiffOn A hA mu hK hcompact hsupp hrho hell hell1 hu i
  have ht := parameterLocalMapTransition_contDiffOn A hA p i
  have hmap := parameterLocalMapTransition_maps A p i
  have hv : ContDiffOn ℝ ∞ v O := hg.comp ht hmap
  have hwBound (k : ℕ) : ‖iteratedFDeriv ℝ k (fun z => w z ^ 2) y‖ ≤
      bufferedCutoffSquareConstant B k := by
    unfold bufferedCutoffSquareConstant
    simpa only [one_pow, mul_one] using norm_iteratedFDeriv_sq_le B hB 1 zero_le_one w O hO hw
      y hy (fun l => by simpa only [one_pow, mul_one] using hweight l) k
  have hvBound (k : ℕ) (hk : k ≤ j) : ‖iteratedFDeriv ℝ k v y‖ ≤
      (k.factorial : ℝ) * R * bufferedTransitionPrefix T k ^ k :=
    buffered_composition_jet_le T hT hO (tensorLocalInner_open A i) ht hg hmap hy k R
      (fun l hl => hlocal l (hl.trans hk)) (fun l hl _ => htransition l hl)
  have hprod := norm_iteratedFDerivWithin_smul_le (hw.pow 2) hv hO.uniqueDiffOn hy
    (n := j) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hO hy] at hprod
  change ‖iteratedFDeriv ℝ j (fun z => w z ^ 2 • v z) y‖ ≤ _
  apply hprod.trans
  calc
    ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun z => w z ^ 2) y‖ *
        ‖iteratedFDeriv ℝ (j - l) v y‖ ≤
      ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * bufferedCutoffSquareConstant B l *
        (((j - l).factorial : ℝ) * R * bufferedTransitionPrefix T (j - l) ^ (j - l)) := by
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hwBound l) (by positivity))
        (hvBound (j - l) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (by positivity) (bufferedCutoffSquareConstant_nonneg hB l))
    _ = bufferedTransferCore B T j * R := by
      unfold bufferedTransferCore
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring

/-- The exact error identity is needed only as a germ at the evaluation
point; the family need not cover the manifold. -/
theorem parameterLocalMapSmoothing_error_chart_eventuallyEq
    (A : TensorBufferedChartFamily ι M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (u : M → F) (p : ι) {y : E}
    (hpartition : ∀ᶠ z in 𝓝 y, ∑ i, chi i ((A.chart p).symm z)^2 = 1) :
    (fun z => parameterLocalMapSmoothing A mu K ell chi u ((A.chart p).symm z) -
      u ((A.chart p).symm z)) =ᶠ[𝓝 y]
      (fun z => ∑ i, parameterLocalMapErrorPullback A mu K ell chi u p i z) := by
  filter_upwards [hpartition] with z hz
  exact parameterLocalMapSmoothing_error_at A mu K ell chi hchiSupport u ((A.chart p).symm z) hz

/-- All native derivatives of the actual global error are controlled by true
local error jets, genuine cutoff/transition providers and actual support
multiplicity. The explicit constant is independent of the total chart count. -/
theorem parameterLocalMapSmoothing_chart_jet_le (A : TensorBufferedChartFamily ι M E)
    (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : ι → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    {u : M → F} (hu : ∀ i, ContDiffOn ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i).target)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (p : ι) {y : E} (hy : y ∈ (A.chart p).target)
    (hpartition : ∀ᶠ z in 𝓝 y, ∑ i, chi i ((A.chart p).symm z)^2 = 1)
    (hD : (activeCutoffIndices chi ((A.chart p).symm y)).card ≤ D)
    (J j : ℕ) (hj : j ≤ J) (R : ℝ) (hR : 0 ≤ R)
    (hweight : ∀ i, (A.chart p).symm y ∈ tsupport (chi i) →
      ∀ k, ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ i, (A.chart p).symm y ∈ tsupport (chi i) →
      ∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hlocal : ∀ i, (A.chart p).symm y ∈ tsupport (chi i) →
      ∀ k ≤ J, ‖iteratedFDeriv ℝ k (parameterLocalMapError A mu K ell u i)
        (A.chart i ((A.chart p).symm y))‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (fun z => parameterLocalMapSmoothing A mu K ell chi u ((A.chart p).symm z) -
      u ((A.chart p).symm z)) y‖ ≤ bufferedTransferConstant B T D J * R := by
  classical
  let S := activeCutoffIndices chi ((A.chart p).symm y)
  have hzero (i : ι) (hi : i ∉ S) :
      parameterLocalMapErrorPullback A mu K ell chi u p i =ᶠ[𝓝 y] (fun _ => (0 : F)) :=
    parameterLocalMapErrorPullback_eventuallyEq_zero A mu K ell chi u p i hy (by simpa [S] using hi)
  have hreg (i : ι) : ContDiffAt ℝ ∞ (parameterLocalMapErrorPullback A mu K ell chi u p i) y := by
    by_cases hi : i ∈ S
    · have hmem : (A.chart p).symm y ∈ tsupport (chi i) := by simpa [S] using hi
      exact (parameterLocalMapErrorPullback_contDiffOn A hA mu hK hcompact hsupp hrho hell hell1 chi hchi hu p i).contDiffAt
        ((parameterLocalMapOverlap_open A p i).mem_nhds ⟨hy, hchiSupport i hmem⟩)
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero i hi)
  have hsum : iteratedFDeriv ℝ j
      (fun z => parameterLocalMapSmoothing A mu K ell chi u ((A.chart p).symm z) - u ((A.chart p).symm z)) y =
      ∑ i, iteratedFDeriv ℝ j (parameterLocalMapErrorPullback A mu K ell chi u p i) y := by
    rw [((parameterLocalMapSmoothing_error_chart_eventuallyEq A mu K ell chi hchiSupport u p hpartition).iteratedFDeriv ℝ j).eq_of_nhds]
    exact iteratedFDeriv_fun_sum_apply (fun i _ => (hreg i).of_le (by simp))
  have hinactive (i : ι) (hi : i ∉ S) :
      iteratedFDeriv ℝ j (parameterLocalMapErrorPullback A mu K ell chi u p i) y = 0 := by
    simpa using ((hzero i hi).iteratedFDeriv ℝ j).eq_of_nhds
  have hfiltered : (∑ i, iteratedFDeriv ℝ j (parameterLocalMapErrorPullback A mu K ell chi u p i) y) =
      ∑ i ∈ S, iteratedFDeriv ℝ j (parameterLocalMapErrorPullback A mu K ell chi u p i) y :=
    (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hinactive i hi)).symm
  rw [hsum, hfiltered]
  calc
    ‖∑ i ∈ S, iteratedFDeriv ℝ j (parameterLocalMapErrorPullback A mu K ell chi u p i) y‖ ≤
      ∑ i ∈ S, ‖iteratedFDeriv ℝ j (parameterLocalMapErrorPullback A mu K ell chi u p i) y‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, bufferedTransferCore B T j * R := by
      apply Finset.sum_le_sum
      intro i hi
      have hmem : (A.chart p).symm y ∈ tsupport (chi i) := by simpa [S] using hi
      exact parameterLocalMapErrorPullback_jet_le A hA mu hK hcompact hsupp hrho hell hell1 chi hchi hu
        B T hB hT p i ⟨hy, hchiSupport i hmem⟩ j R hR (hweight i hmem) (htransition i hmem)
        (fun k hk => hlocal i hmem k (hk.trans hj))
    _ = (S.card : ℝ) * (bufferedTransferCore B T j * R) := by simp
    _ ≤ (D : ℝ) * (bufferedTransferCore B T j * R) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hD)
        (mul_nonneg (bufferedTransferCore_nonneg hB hT j) hR)
    _ ≤ bufferedTransferConstant B T D J * R := by
      unfold bufferedTransferConstant
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hR
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg D)
      exact Finset.single_le_sum (fun k _ => bufferedTransferCore_nonneg hB hT k)
        (by simpa using hj)

#print axioms parameterLocalMapSmoothing_chart_jet_le
#print axioms parameterLocalMapErrorPullback_jet_le
end BufferedJets

end

end GlobalEmbedding.Continuation
