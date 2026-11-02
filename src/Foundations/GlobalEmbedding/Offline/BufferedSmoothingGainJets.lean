import GlobalEmbedding.Offline.BufferedSmoothingJets

/-!
# Native localization of the actual global smoother for derivative gain

Source: `main.tex` 700–720, the derivative-gain step of buffered localization.
The same original global convolution sum is differentiated directly, with
all actual cutoff and transition terms and genuine support multiplicity.
This lemma complements the error localization: it does not differentiate the
unsmoothed source when bounding the smoother's additional derivatives.
-/

open MeasureTheory GlobalEmbedding.Paper Function Filter Set Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Offline

noncomputable section

variable {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- An actual smoothing summand in an actual receiving chart. -/
def bufferedSmoothingPullback (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ) (u : M → F)
    (p i : Fin A.count) : E → F :=
  fun y => chi i ((A.chart p).symm y) ^ 2 •
    bufferedLocalSmoothing A mu K ell u i (A.chart i ((A.chart p).symm y))

/-- Native regularity on each actual active overlap. -/
theorem bufferedSmoothingPullback_contDiffOn (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    {u : M → F} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u) (p i : Fin A.count) :
    ContDiffOn ℝ ∞ (bufferedSmoothingPullback A mu K ell chi u p i) (bufferedChartOverlap A p i) := by
  have hweight : ContDiffOn ℝ ∞ (chi i ∘ (A.chart p).symm) (bufferedChartOverlap A p i) :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem p))).contDiffOn.mono
      (fun _ hy => hy.1)
  exact (hweight.pow 2).smul ((bufferedLocalSmoothing_contDiffOn A hA mu hK hcompact hsupp hrho
    hell hell1 hu i).comp (bufferedTransition_contDiffOn A hA p i) (bufferedTransition_maps A p i))

omit [BorelSpace E] [FiniteDimensional ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Off an actual cutoff support, every smoothing summand has a genuine zero germ. -/
theorem bufferedSmoothingPullback_eventuallyEq_zero (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ) (u : M → F)
    (p i : Fin A.count) {y : E} (hy : y ∈ (A.chart p).target)
    (hi : (A.chart p).symm y ∉ tsupport (chi i)) :
    bufferedSmoothingPullback A mu K ell chi u p i =ᶠ[𝓝 y] (fun _ => (0 : F)) := by
  filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hi).comp_tendsto
    ((A.chart p).symm.continuousAt hy)] with z hz
  change chi i ((A.chart p).symm z) = 0 at hz
  simp only [bufferedSmoothingPullback, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_smul]

/-- The actual cutoff and transition derivative providers control one active
summand by an explicit constant times the actual local smoothing-jet bound. -/
theorem bufferedSmoothingPullback_jet_le (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    {u : M → F} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j)
    (p i : Fin A.count) {y : E} (hy : y ∈ bufferedChartOverlap A p i)
    (j : ℕ) (R : ℝ) (_hR : 0 ≤ R)
    (hweight : ∀ k, ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hlocal : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (bufferedLocalSmoothing A mu K ell u i)
      (A.chart i ((A.chart p).symm y))‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (bufferedSmoothingPullback A mu K ell chi u p i) y‖ ≤
      bufferedTransferCore B T j * R := by
  let O := bufferedChartOverlap A p i
  let w := chi i ∘ (A.chart p).symm
  let v := bufferedLocalSmoothing A mu K ell u i ∘ (A.chart i ∘ (A.chart p).symm)
  have hO : IsOpen O := bufferedChartOverlap_open A p i
  have hw : ContDiffOn ℝ ∞ w O :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem p))).contDiffOn.mono
      (fun _ hz => hz.1)
  have hg := bufferedLocalSmoothing_contDiffOn A hA mu hK hcompact hsupp hrho hell hell1 hu i
  have ht := bufferedTransition_contDiffOn A hA p i
  have hmap := bufferedTransition_maps A p i
  have hv : ContDiffOn ℝ ∞ v O := hg.comp ht hmap
  have hwBound (k : ℕ) : ‖iteratedFDeriv ℝ k (fun z => w z ^ 2) y‖ ≤
      bufferedCutoffSquareConstant B k := by
    unfold bufferedCutoffSquareConstant
    simpa only [one_pow, mul_one] using norm_iteratedFDeriv_sq_le B hB 1 zero_le_one w O hO hw
      y hy (fun l => by simpa only [one_pow, mul_one] using hweight l) k
  have hvBound (k : ℕ) (hk : k ≤ j) : ‖iteratedFDeriv ℝ k v y‖ ≤
      (k.factorial : ℝ) * R * bufferedTransitionPrefix T k ^ k :=
    buffered_composition_jet_le T hT hO (bufferedInnerCoordinates_open A i) ht hg hmap hy k R
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

omit [BorelSpace E] [FiniteDimensional ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The SAME global smoother, in the actual receiving chart, is exactly the sum
of the genuine transitioned local smoothings. No independently glued jet is used. -/
theorem bufferedSmoothing_chart_eq (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (u : M → F) (p : Fin A.count) :
    (fun y => bufferedSmoothing A mu K ell chi u ((A.chart p).symm y)) =
      fun y => ∑ i, bufferedSmoothingPullback A mu K ell chi u p i y := by
  funext y
  change (∑ i, bufferedSmoothingTerm A mu K ell chi u i ((A.chart p).symm y)) = _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : chi i ((A.chart p).symm y) = 0
  · simp only [bufferedSmoothingTerm, bufferedSmoothingPullback, hi,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_smul]
  · have hx := A.inner_subset i (hchiSupport i (subset_tsupport (chi i) hi))
    simp only [bufferedSmoothingTerm, bufferedChartSmoothing,
      Set.indicator_of_mem hx, Function.comp_apply, bufferedSmoothingPullback]

/-- All native derivatives of the actual global smoother are controlled by true
local smoothing jets, genuine cutoff/transition providers and actual support
multiplicity. The explicit constant is independent of the total chart count. -/
theorem bufferedSmoothing_gain_chart_jet_le (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    {u : M → F} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (p : Fin A.count) {y : E} (hy : y ∈ (A.chart p).target)
    (hD : (activeCutoffIndices chi ((A.chart p).symm y)).card ≤ D)
    (J j : ℕ) (hj : j ≤ J) (R : ℝ) (hR : 0 ≤ R)
    (hweight : ∀ i, (A.chart p).symm y ∈ tsupport (chi i) →
      ∀ k, ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ i, (A.chart p).symm y ∈ tsupport (chi i) →
      ∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hlocal : ∀ i, (A.chart p).symm y ∈ tsupport (chi i) →
      ∀ k ≤ J, ‖iteratedFDeriv ℝ k (bufferedLocalSmoothing A mu K ell u i)
        (A.chart i ((A.chart p).symm y))‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (fun z => bufferedSmoothing A mu K ell chi u ((A.chart p).symm z)) y‖ ≤ bufferedTransferConstant B T D J * R := by
  classical
  let S := activeCutoffIndices chi ((A.chart p).symm y)
  have hzero (i : Fin A.count) (hi : i ∉ S) :
      bufferedSmoothingPullback A mu K ell chi u p i =ᶠ[𝓝 y] (fun _ => (0 : F)) :=
    bufferedSmoothingPullback_eventuallyEq_zero A mu K ell chi u p i hy (by simpa [S] using hi)
  have hreg (i : Fin A.count) : ContDiffAt ℝ ∞ (bufferedSmoothingPullback A mu K ell chi u p i) y := by
    by_cases hi : i ∈ S
    · have hmem : (A.chart p).symm y ∈ tsupport (chi i) := by simpa [S] using hi
      exact (bufferedSmoothingPullback_contDiffOn A hA mu hK hcompact hsupp hrho hell hell1 chi hchi hu p i).contDiffAt
        ((bufferedChartOverlap_open A p i).mem_nhds ⟨hy, hchiSupport i hmem⟩)
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero i hi)
  have hsum : iteratedFDeriv ℝ j
      (fun z => bufferedSmoothing A mu K ell chi u ((A.chart p).symm z)) y =
      ∑ i, iteratedFDeriv ℝ j (bufferedSmoothingPullback A mu K ell chi u p i) y := by
    rw [bufferedSmoothing_chart_eq A mu K ell chi hchiSupport u p]
    exact iteratedFDeriv_fun_sum_apply (fun i _ => (hreg i).of_le (by simp))
  have hinactive (i : Fin A.count) (hi : i ∉ S) :
      iteratedFDeriv ℝ j (bufferedSmoothingPullback A mu K ell chi u p i) y = 0 := by
    simpa using ((hzero i hi).iteratedFDeriv ℝ j).eq_of_nhds
  have hfiltered : (∑ i, iteratedFDeriv ℝ j (bufferedSmoothingPullback A mu K ell chi u p i) y) =
      ∑ i ∈ S, iteratedFDeriv ℝ j (bufferedSmoothingPullback A mu K ell chi u p i) y :=
    (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hinactive i hi)).symm
  rw [hsum, hfiltered]
  calc
    ‖∑ i ∈ S, iteratedFDeriv ℝ j (bufferedSmoothingPullback A mu K ell chi u p i) y‖ ≤
      ∑ i ∈ S, ‖iteratedFDeriv ℝ j (bufferedSmoothingPullback A mu K ell chi u p i) y‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, bufferedTransferCore B T j * R := by
      apply Finset.sum_le_sum
      intro i hi
      have hmem : (A.chart p).symm y ∈ tsupport (chi i) := by simpa [S] using hi
      exact bufferedSmoothingPullback_jet_le A hA mu hK hcompact hsupp hrho hell hell1 chi hchi hu
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


end

end GlobalEmbedding.Offline
