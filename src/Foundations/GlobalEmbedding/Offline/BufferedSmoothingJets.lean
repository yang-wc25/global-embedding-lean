import GlobalEmbedding.Offline.BufferedSmoothing
import GlobalEmbedding.Offline.BoundedSquareCutoffSum

/-!
# Actual derivatives of the globally glued smoothing error

Source: `main.tex` 700–720, the cutoff/transition and overlap steps of
`repair-buffered-smoothing-localization`. Every derivative below belongs to
the same original buffered smoothing map. True chart transitions enter the
native composition estimate, true cutoff squares enter native Leibniz, and
terms outside the actual topological support have zero germs. Constants are
explicit finite expressions in derivative-provider bounds and multiplicity;
they have no atlas/index-type parameter.
-/

open MeasureTheory GlobalEmbedding.Paper Function Filter Set Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Offline

noncomputable section

/-- Explicit cutoff-square coefficient from native Leibniz. -/
def bufferedCutoffSquareConstant (B : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * B l * B (j - l)

/-- One fixed bound for the positive-order transition derivatives used at order j. -/
def bufferedTransitionPrefix (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  1 + ∑ l ∈ Finset.range (j + 1), T l

/-- Actual cutoff-square/product/composition coefficient at one derivative order. -/
def bufferedTransferCore (B T : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * bufferedCutoffSquareConstant B l *
    ((j - l).factorial : ℝ) * bufferedTransitionPrefix T (j - l) ^ (j - l)

/-- Cumulative transfer constant with actual support multiplicity D.
Its type is independent of all charts, chart counts, scales and fields. -/
def bufferedTransferConstant (B T : ℕ → ℝ) (D j : ℕ) : ℝ :=
  (D : ℝ) * ∑ k ∈ Finset.range (j + 1), bufferedTransferCore B T k

theorem bufferedCutoffSquareConstant_nonneg {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (j : ℕ) :
    0 ≤ bufferedCutoffSquareConstant B j :=
  Finset.sum_nonneg fun l _ => mul_nonneg (mul_nonneg (by positivity) (hB l)) (hB _)

theorem one_le_bufferedTransitionPrefix {T : ℕ → ℝ} (hT : ∀ j, 0 ≤ T j) (j : ℕ) :
    1 ≤ bufferedTransitionPrefix T j := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun l _ => hT l)

theorem bufferedTransferCore_nonneg {B T : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (j : ℕ) :
    0 ≤ bufferedTransferCore B T j := by
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg (mul_nonneg
    (mul_nonneg (by positivity) (bufferedCutoffSquareConstant_nonneg hB l)) (by positivity))
    (pow_nonneg (zero_le_one.trans (one_le_bufferedTransitionPrefix hT _)) _)

theorem bufferedTransferConstant_nonneg {B T : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D j : ℕ) :
    0 ≤ bufferedTransferConstant B T D j :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun k _ => bufferedTransferCore_nonneg hB hT k)

theorem bufferedTransferConstant_mono {B T : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ) {a b : ℕ} (hab : a ≤ b) :
    bufferedTransferConstant B T D a ≤ bufferedTransferConstant B T D b := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg D)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.add_le_add_right hab 1)
  · intro k _ _
    exact bufferedTransferCore_nonneg hB hT k

section Composition

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A direct use of the native all-order composition bound, retaining an
explicit provider-only constant and a linear dependence on the outer error R. -/
theorem buffered_composition_jet_le (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    {f : E → E} {g : E → F} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo f U V)
    {x : E} (hx : x ∈ U) (j : ℕ) (R : ℝ)
    (houter : ∀ k ≤ j, ‖iteratedFDeriv ℝ k g (f x)‖ ≤ R)
    (hinner : ∀ k, 1 ≤ k → k ≤ j → ‖iteratedFDeriv ℝ k f x‖ ≤ T k) :
    ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤
      (j.factorial : ℝ) * R * bufferedTransitionPrefix T j ^ j := by
  have hQ := one_le_bufferedTransitionPrefix hT j
  have hin (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) :
      ‖iteratedFDerivWithin ℝ k f U x‖ ≤ bufferedTransitionPrefix T j ^ k := by
    rw [iteratedFDerivWithin_of_isOpen k hU hx]
    have hsum : T k ≤ ∑ l ∈ Finset.range (j + 1), T l :=
      Finset.single_le_sum (fun l _ => hT l) (by simpa using hkj)
    have hTQ : T k ≤ bufferedTransitionPrefix T j := by
      unfold bufferedTransitionPrefix
      linarith
    exact (hinner k hk hkj).trans (hTQ.trans (le_self_pow₀ hQ (by omega)))
  have hout (k : ℕ) (hk : k ≤ j) : ‖iteratedFDerivWithin ℝ k g V (f x)‖ ≤ R := by
    rw [iteratedFDerivWithin_of_isOpen k hV (hmap hx)]
    exact houter k hk
  have h := norm_iteratedFDerivWithin_comp_le hg hf (n := j) (by simp)
    hV.uniqueDiffOn hU.uniqueDiffOn hmap hx hout hin
  rwa [iteratedFDerivWithin_of_isOpen j hU hx] at h

end Composition

section BufferedJets

variable {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual local error used in the global identity. -/
def bufferedLocalError (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (u : M → F) (i : Fin A.count) : E → F :=
  bufferedLocalSmoothing A mu K ell u i - bufferedCoordinateExtension A u i

/-- A receiving chart's genuine overlap with an original inner domain. -/
def bufferedChartOverlap (A : BufferedAtlas M E) (p i : Fin A.count) : Set E :=
  (A.chart p).target ∩ (A.chart p).symm ⁻¹' A.inner i

/-- One genuine summand of the global error in the receiving chart. -/
def bufferedErrorPullback (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ) (u : M → F)
    (p i : Fin A.count) : E → F :=
  fun y => chi i ((A.chart p).symm y) ^ 2 •
    bufferedLocalError A mu K ell u i (A.chart i ((A.chart p).symm y))

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem bufferedChartOverlap_open (A : BufferedAtlas M E) (p i : Fin A.count) :
    IsOpen (bufferedChartOverlap A p i) :=
  (A.chart p).isOpen_inter_preimage_symm (A.inner_open i)

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem bufferedTransition_maps (A : BufferedAtlas M E) (p i : Fin A.count) :
    MapsTo (A.chart i ∘ (A.chart p).symm) (bufferedChartOverlap A p i)
      (bufferedInnerCoordinates A i) :=
  fun _ hy => bufferedInnerCoordinates_mem A i hy.2

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem bufferedTransition_contDiffOn (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (p i : Fin A.count) :
    ContDiffOn ℝ ∞ (A.chart i ∘ (A.chart p).symm) (bufferedChartOverlap A p i) := by
  exact ((contMDiffOn_of_mem_maximalAtlas (hA.chart_mem i)).comp
    ((contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem p)).mono (fun _ hy => hy.1))
      (fun _ hy => A.inner_subset i hy.2)).contDiffOn

theorem bufferedLocalError_contDiffOn (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    {u : M → F} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (bufferedLocalError A mu K ell u i) (bufferedInnerCoordinates A i) :=
  (bufferedLocalSmoothing_contDiffOn A hA mu hK hcompact hsupp hrho hell hell1 hu i).sub
    ((bufferedCoordinateExtension_contDiffOn A hA hu i).mono (fun _ hy => hy.1))

/-- Native regularity on each actual active overlap. -/
theorem bufferedErrorPullback_contDiffOn (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    {u : M → F} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u) (p i : Fin A.count) :
    ContDiffOn ℝ ∞ (bufferedErrorPullback A mu K ell chi u p i) (bufferedChartOverlap A p i) := by
  have hweight : ContDiffOn ℝ ∞ (chi i ∘ (A.chart p).symm) (bufferedChartOverlap A p i) :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem p))).contDiffOn.mono
      (fun _ hy => hy.1)
  exact (hweight.pow 2).smul ((bufferedLocalError_contDiffOn A hA mu hK hcompact hsupp hrho
    hell hell1 hu i).comp (bufferedTransition_contDiffOn A hA p i) (bufferedTransition_maps A p i))

omit [BorelSpace E] [FiniteDimensional ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Off an actual cutoff support, every error summand has a genuine zero germ. -/
theorem bufferedErrorPullback_eventuallyEq_zero (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ) (u : M → F)
    (p i : Fin A.count) {y : E} (hy : y ∈ (A.chart p).target)
    (hi : (A.chart p).symm y ∉ tsupport (chi i)) :
    bufferedErrorPullback A mu K ell chi u p i =ᶠ[𝓝 y] (fun _ => (0 : F)) := by
  filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hi).comp_tendsto
    ((A.chart p).symm.continuousAt hy)] with z hz
  change chi i ((A.chart p).symm z) = 0 at hz
  simp only [bufferedErrorPullback, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_smul]

/-- The actual cutoff and transition derivative providers control one active
summand by an explicit constant times the actual local error-jet bound. -/
theorem bufferedErrorPullback_jet_le (A : BufferedAtlas M E)
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
    (hlocal : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (bufferedLocalError A mu K ell u i)
      (A.chart i ((A.chart p).symm y))‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (bufferedErrorPullback A mu K ell chi u p i) y‖ ≤
      bufferedTransferCore B T j * R := by
  let O := bufferedChartOverlap A p i
  let w := chi i ∘ (A.chart p).symm
  let v := bufferedLocalError A mu K ell u i ∘ (A.chart i ∘ (A.chart p).symm)
  have hO : IsOpen O := bufferedChartOverlap_open A p i
  have hw : ContDiffOn ℝ ∞ w O :=
    ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem p))).contDiffOn.mono
      (fun _ hz => hz.1)
  have hg := bufferedLocalError_contDiffOn A hA mu hK hcompact hsupp hrho hell hell1 hu i
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
/-- The SAME global error, in the actual receiving chart, is exactly the sum
of the genuine transitioned local errors. No independently glued jet is used. -/
theorem bufferedSmoothing_error_chart_eq (A : BufferedAtlas M E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1) (u : M → F) (p : Fin A.count) :
    (fun y => bufferedSmoothing A mu K ell chi u ((A.chart p).symm y) - u ((A.chart p).symm y)) =
      fun y => ∑ i, bufferedErrorPullback A mu K ell chi u p i y := by
  funext y
  exact bufferedSmoothing_error_eq A mu K ell chi hchiSupport hpartition u ((A.chart p).symm y)

/-- All native derivatives of the actual global error are controlled by true
local error jets, genuine cutoff/transition providers and actual support
multiplicity. The explicit constant is independent of the total chart count. -/
theorem bufferedSmoothing_chart_jet_le (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
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
      ∀ k ≤ J, ‖iteratedFDeriv ℝ k (bufferedLocalError A mu K ell u i)
        (A.chart i ((A.chart p).symm y))‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (fun z => bufferedSmoothing A mu K ell chi u ((A.chart p).symm z) -
      u ((A.chart p).symm z)) y‖ ≤ bufferedTransferConstant B T D J * R := by
  classical
  let S := activeCutoffIndices chi ((A.chart p).symm y)
  have hzero (i : Fin A.count) (hi : i ∉ S) :
      bufferedErrorPullback A mu K ell chi u p i =ᶠ[𝓝 y] (fun _ => (0 : F)) :=
    bufferedErrorPullback_eventuallyEq_zero A mu K ell chi u p i hy (by simpa [S] using hi)
  have hreg (i : Fin A.count) : ContDiffAt ℝ ∞ (bufferedErrorPullback A mu K ell chi u p i) y := by
    by_cases hi : i ∈ S
    · have hmem : (A.chart p).symm y ∈ tsupport (chi i) := by simpa [S] using hi
      exact (bufferedErrorPullback_contDiffOn A hA mu hK hcompact hsupp hrho hell hell1 chi hchi hu p i).contDiffAt
        ((bufferedChartOverlap_open A p i).mem_nhds ⟨hy, hchiSupport i hmem⟩)
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero i hi)
  have hsum : iteratedFDeriv ℝ j
      (fun z => bufferedSmoothing A mu K ell chi u ((A.chart p).symm z) - u ((A.chart p).symm z)) y =
      ∑ i, iteratedFDeriv ℝ j (bufferedErrorPullback A mu K ell chi u p i) y := by
    rw [bufferedSmoothing_error_chart_eq A mu K ell chi hchiSupport hpartition u p]
    exact iteratedFDeriv_fun_sum_apply (fun i _ => (hreg i).of_le (by simp))
  have hinactive (i : Fin A.count) (hi : i ∉ S) :
      iteratedFDeriv ℝ j (bufferedErrorPullback A mu K ell chi u p i) y = 0 := by
    simpa using ((hzero i hi).iteratedFDeriv ℝ j).eq_of_nhds
  have hfiltered : (∑ i, iteratedFDeriv ℝ j (bufferedErrorPullback A mu K ell chi u p i) y) =
      ∑ i ∈ S, iteratedFDeriv ℝ j (bufferedErrorPullback A mu K ell chi u p i) y :=
    (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hinactive i hi)).symm
  rw [hsum, hfiltered]
  calc
    ‖∑ i ∈ S, iteratedFDeriv ℝ j (bufferedErrorPullback A mu K ell chi u p i) y‖ ≤
      ∑ i ∈ S, ‖iteratedFDeriv ℝ j (bufferedErrorPullback A mu K ell chi u p i) y‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, bufferedTransferCore B T j * R := by
      apply Finset.sum_le_sum
      intro i hi
      have hmem : (A.chart p).symm y ∈ tsupport (chi i) := by simpa [S] using hi
      exact bufferedErrorPullback_jet_le A hA mu hK hcompact hsupp hrho hell hell1 chi hchi hu
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

end BufferedJets

end

end GlobalEmbedding.Offline
