import Smoothing.ParameterProductAtlas
import Smoothing.ParameterTransferBounds

/-!
# Genuine global anisotropic error jets on a nonzero-parameter product atlas

The global function is the original bufferedSmoothing on the actual product
atlas. Its spatial two-jet is differentiated only after this map is glued.
True product transitions, cutoff Hessians and active support multiplicity
enter an explicit bound independent of total atlas cardinality.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Filter Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {Ep Es P M Y : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es]
    [TopologicalSpace P] [TopologicalSpace M]
    [ChartedSpace Ep P] [IsManifold 𝓘(ℝ, Ep) ∞ P]
    [ChartedSpace Es M] [IsManifold 𝓘(ℝ, Es) ∞ M]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
local instance : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M

variable (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
local notation "AB" => parameterProductAtlas A B

/-- The actual product overlap is a product of the original two overlaps. -/
theorem parameterProductAtlas_overlap (p i : Fin (B.count * A.count)) :
    bufferedChartOverlap AB p i =
      bufferedChartOverlap B (parameterProductIndex A B p).1 (parameterProductIndex A B i).1 ×ˢ
      bufferedChartOverlap A (parameterProductIndex A B p).2 (parameterProductIndex A B i).2 := by
  ext z
  simp only [bufferedChartOverlap, parameterProductAtlas, Set.mem_inter_iff,
    Set.mem_preimage, OpenPartialHomeomorph.prod_target, OpenPartialHomeomorph.prod_symm,
    OpenPartialHomeomorph.prod_apply, Set.mem_prod]
  tauto

variable [FiniteDimensional ℝ Es] [FiniteDimensional ℝ Y]
attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

/-- The real geometric operator in the receiving product chart. -/
def parameterBufferedTransfer (chi : Fin (B.count * A.count) → P × M → ℝ)
    (p i : Fin (B.count * A.count)) : Ep × Es → SpatialNativeJet Es Y →L[ℝ] SpatialNativeJet Es Y :=
  spatialTransferField (fun z => chi i (((AB).chart p).symm z) ^ 2)
    (A.chart (parameterProductIndex A B i).2 ∘ (A.chart (parameterProductIndex A B p).2).symm)

variable [MeasurableSpace Ep] [BorelSpace Ep] [FiniteDimensional ℝ Ep]
    [MeasurableSpace Es] [BorelSpace Es]
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (mu : Measure (Ep × Es)) [mu.IsAddHaarMeasure]

include hA hB

/-- One actual localized error term obeys the genuine source-two-jet estimate. -/
theorem parameterBufferedError_spatial_jet_le
    {K : Ep × Es → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin (B.count * A.count) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    {u : P × M → Y} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Y) ∞ u)
    (C T : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 ≤ T k)
    (p i : Fin (B.count * A.count)) {z : Ep × Es} (hz : z ∈ bufferedChartOverlap AB p i)
    (j : ℕ) (R : ℝ)
    (hcoeff : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (parameterBufferedTransfer (Y := Y) A B chi p i) z‖ ≤ C k)
    (htransition : ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k ((AB).chart i ∘ ((AB).chart p).symm) z‖ ≤ T k)
    (hlocal : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (spatialNativeJet (bufferedLocalError AB mu K ell u i))
      ((AB).chart i (((AB).chart p).symm z))‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (spatialNativeJet (bufferedErrorPullback AB mu K ell chi u p i)) z‖ ≤
      parameterJetTransferCore C T j * R := by
  have hAB := parameterProductAtlas_smooth A B hA hB
  have hOp := bufferedChartOverlap_open B (parameterProductIndex A B p).1 (parameterProductIndex A B i).1
  have hOs := bufferedChartOverlap_open A (parameterProductIndex A B p).2 (parameterProductIndex A B i).2
  have hV := bufferedInnerCoordinates_open AB i
  have hu' := bufferedLocalError_contDiffOn AB hAB mu hK hcompact hsupp hrho hell hell1 hu i
  have ha := bufferedTransition_contDiffOn B hB (parameterProductIndex A B p).1 (parameterProductIndex A B i).1
  have hb := bufferedTransition_contDiffOn A hA (parameterProductIndex A B p).2 (parameterProductIndex A B i).2
  have hw : ContDiffOn ℝ ∞ (fun z => chi i (((AB).chart p).symm z)^2) (bufferedChartOverlap AB p i) :=
    by
      letI : ChartedSpace (Ep × Es) (Ep × Es) := chartedSpaceSelf (Ep × Es)
      exact (((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hAB.chart_mem p))).contDiffOn.mono
        (fun _ h => h.1)).pow 2
  rw [parameterProductAtlas_overlap A B p i] at hw hz
  have hmap : ∀ a ∈ bufferedChartOverlap B (parameterProductIndex A B p).1 (parameterProductIndex A B i).1,
      ∀ b ∈ bufferedChartOverlap A (parameterProductIndex A B p).2 (parameterProductIndex A B i).2,
      ((B.chart (parameterProductIndex A B i).1 ∘ (B.chart (parameterProductIndex A B p).1).symm) a,
       (A.chart (parameterProductIndex A B i).2 ∘ (A.chart (parameterProductIndex A B p).2).symm) b) ∈
        bufferedInnerCoordinates AB i := by
    intro a ha b hb
    apply bufferedTransition_maps AB p i (x := (a,b))
    rw [parameterProductAtlas_overlap A B p i]
    exact ⟨ha,hb⟩
  exact parameter_spatial_transfer_jet_le C T hC hT hOp hOs hV hw hu' ha hb hmap hz j R
    hcoeff htransition hlocal

/-- Every additional joint derivative of the same global map error's spatial
two-jet is controlled with the true active overlap multiplicity. -/
theorem parameterBufferedSmoothing_spatial_jet_le
    {K : Ep × Es → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin (B.count * A.count) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (AB).inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : P × M → Y} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Y) ∞ u)
    (C T : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 ≤ T k) (D : ℕ)
    (p : Fin (B.count * A.count)) {z : Ep × Es} (hz : z ∈ ((AB).chart p).target)
    (hD : (activeCutoffIndices chi (((AB).chart p).symm z)).card ≤ D)
    (J j : ℕ) (hj : j ≤ J) (R : ℝ) (hR : 0 ≤ R)
    (hcoeff : ∀ i, ((AB).chart p).symm z ∈ tsupport (chi i) →
      ∀ k ≤ j, ‖iteratedFDeriv ℝ k (parameterBufferedTransfer (Y := Y) A B chi p i) z‖ ≤ C k)
    (htransition : ∀ i, ((AB).chart p).symm z ∈ tsupport (chi i) →
      ∀ k, 1 ≤ k → k ≤ j → ‖iteratedFDeriv ℝ k ((AB).chart i ∘ ((AB).chart p).symm) z‖ ≤ T k)
    (hlocal : ∀ i, ((AB).chart p).symm z ∈ tsupport (chi i) →
      ∀ k ≤ J, ‖iteratedFDeriv ℝ k (spatialNativeJet (bufferedLocalError AB mu K ell u i))
        ((AB).chart i (((AB).chart p).symm z))‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (spatialNativeJet (fun y =>
      bufferedSmoothing AB mu K ell chi u (((AB).chart p).symm y) - u (((AB).chart p).symm y))) z‖ ≤
      parameterJetTransferConstant C T D J * R := by
  classical
  have hAB := parameterProductAtlas_smooth A B hA hB
  let S := activeCutoffIndices chi (((AB).chart p).symm z)
  let f := bufferedErrorPullback AB mu K ell chi u p
  have hreg (y : Ep × Es) (hy : y ∈ ((AB).chart p).target) (i : Fin (B.count*A.count)) :
      ContDiffAt ℝ ∞ (f i) y := by
    by_cases hi : ((AB).chart p).symm y ∈ tsupport (chi i)
    · exact (bufferedErrorPullback_contDiffOn AB hAB mu hK hcompact hsupp hrho hell hell1 chi hchi hu p i).contDiffAt
        ((bufferedChartOverlap_open AB p i).mem_nhds ⟨hy,hchiSupport i hi⟩)
    · exact contDiffAt_const.congr_of_eventuallyEq
        (bufferedErrorPullback_eventuallyEq_zero AB mu K ell chi u p i hy hi)
  have heq : spatialNativeJet (fun y =>
      bufferedSmoothing AB mu K ell chi u (((AB).chart p).symm y) - u (((AB).chart p).symm y)) =ᶠ[𝓝 z]
      (fun y => ∑ i, spatialNativeJet (f i) y) := by
    rw [bufferedSmoothing_error_chart_eq AB mu K ell chi hchiSupport hpartition u p]
    filter_upwards [((AB).chart p).open_target.mem_nhds hz] with y hy
    exact spatialNativeJet_sum f (hreg y hy)
  rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
  have hzero (i : Fin (B.count*A.count)) (hi : i ∉ S) :
      spatialNativeJet (f i) =ᶠ[𝓝 z] (fun _ => 0) := by
    have hh := spatialNativeJet_eventuallyEq
      (bufferedErrorPullback_eventuallyEq_zero AB mu K ell chi u p i hz (by simpa [S] using hi))
    filter_upwards [hh] with y hy
    exact hy.trans (congrFun spatialNativeJet_zero y)
  have hbound (i : Fin (B.count*A.count)) (hi : i ∈ S) :
      ‖iteratedFDeriv ℝ j (spatialNativeJet (f i)) z‖ ≤ parameterJetTransferCore C T j * R := by
    have hm : ((AB).chart p).symm z ∈ tsupport (chi i) :=
      (mem_activeCutoffIndices chi (((AB).chart p).symm z) i).mp hi
    exact parameterBufferedError_spatial_jet_le A B hA hB mu hK hcompact hsupp hrho hell hell1
      chi hchi hu C T hC hT p i ⟨hz,hchiSupport i hm⟩ j R (hcoeff i hm)
      (htransition i hm) (fun k hk => hlocal i hm k (hk.trans hj))
  apply (parameter_finite_sum_jet_le (fun i => spatialNativeJet (f i)) z S D j
    (parameterJetTransferCore C T j * R) hD
    (mul_nonneg (parameterJetTransferCore_nonneg hC hT j) hR) ?_ hzero hbound).trans
  · unfold parameterJetTransferConstant
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hR
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg D)
    exact Finset.single_le_sum (fun k _ => parameterJetTransferCore_nonneg hC hT k)
      (by simpa using hj)
  · intro i hi
    have hm : ((AB).chart p).symm z ∈ tsupport (chi i) :=
      (mem_activeCutoffIndices chi (((AB).chart p).symm z) i).mp hi
    exact (spatialNativeJet_contDiffOn (bufferedChartOverlap_open AB p i)
      (bufferedErrorPullback_contDiffOn AB hAB mu hK hcompact hsupp hrho hell hell1 chi hchi hu p i)).contDiffAt
      ((bufferedChartOverlap_open AB p i).mem_nhds ⟨hz,hchiSupport i hm⟩)

#print axioms parameterBufferedError_spatial_jet_le
#print axioms parameterBufferedSmoothing_spatial_jet_le

end
end GlobalEmbedding.Continuation
