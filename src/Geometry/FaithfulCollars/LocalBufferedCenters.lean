import FaithfulCollars.ChartCenterRaw
import Repair.SourceCollarNovFiniteCover
import Smoothing.TensorLocalModelDomains

/-!
# Finite centers for a general original local parameter family

The proof uses the original bounded coordinate inners and the fixed scale.
It does not require any global cover of P or compactness of P.  There is no
restriction on where the original coordinate inners are centered or on
their shape.  The actual centers and their count are outputs.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {ι E P : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace P]

structure OriginalLocalBufferedCenters
    (B : TensorBufferedChartFamily ι P E) (R b : ℝ) (hb : 0 < b) where
  centers : ι → Finset E
  center_inner : ∀ i, (↑(centers i) : Set E) ⊆ tensorLocalInner B i
  separated : ∀ i, ∀ a ∈ centers i, ∀ c ∈ centers i, a ≠ c → b/8 ≤ dist a c
  count_le : ∀ i, (centers i).card ≤ sourceCollarNovPieceBound E R b hb
  covers : ∀ i y, y ∈ tensorLocalInner B i → ∃ c ∈ centers i, dist y c ≤ b/8

theorem originalLocalBufferedCenters_construct
    (R b : ℝ) (hb : 0 < b) (B : TensorBufferedChartFamily ι P E)
    (hRadius : ∀ i y, y ∈ tensorLocalInner B i → ‖y‖ ≤ R) :
    Nonempty (OriginalLocalBufferedCenters B R b hb) := by
  classical
  have hr : 0 < b/8 := by positivity
  have hInnerBall (i : ι) : tensorLocalInner B i ⊆ closedBall (0 : E) R := by
    intro y hy
    simpa only [mem_closedBall, dist_zero_right] using hRadius i y hy
  have hCenters (i : ι) := actual_exists_finite_bounded_refinement (tensorLocalInner B i)
    ((isCompact_closedBall (0 : E) R).totallyBounded.subset (hInnerBall i)) (b/8) hr
  choose centers hSubset hSeparated hCover hLocal using hCenters
  refine ⟨⟨centers, hSubset, hSeparated, ?_, hCover⟩⟩
  intro i
  apply Classical.choose_spec (actual_exists_uniform_total_refinement_bound E R (b/8) hr)
    (centers i) 0
  · intro c hc
    exact hInnerBall i (hSubset i hc)
  · exact hSeparated i

variable (B : TensorBufferedChartFamily ι P E) (R b : ℝ) (hb : 0 < b)
  (hbuffer : b ≤ B.buffer) (s : OriginalLocalBufferedCenters B R b hb)

def localRefinedWorkingDomain (i : ι) : Set E :=
  ⋃ c : s.centers i, ball c.val (3*b/8)

def originalRefinedLocalFamily : TensorBufferedChartFamily ι P E where
  chart := B.chart
  inner i := (B.chart i).source ∩ (B.chart i) ⁻¹' localRefinedWorkingDomain B R b hb s i
  inner_open i := (B.chart i).isOpen_inter_preimage (isOpen_iUnion fun _ => isOpen_ball)
  inner_subset _ := inter_subset_left
  buffer := b/8
  buffer_pos := by positivity
  buffered := by
    intro i p hp y hy
    obtain ⟨c, hc⟩ := mem_iUnion.mp hp.2
    apply tensorLocalSampling_subset_target B i
    apply mem_iUnion.mpr
    refine ⟨c.val, mem_iUnion.mpr ⟨s.center_inner i c.property, ?_⟩⟩
    have hc' : dist (B.chart i p) c.val < 3*b/8 := hc
    have hy' : dist y (B.chart i p) < b/8 := hy
    change dist y c.val < B.buffer
    linarith [dist_triangle y (B.chart i p) c.val]

theorem refinedLocalFamily_chart_eq :
    (originalRefinedLocalFamily B R b hb hbuffer s).chart = B.chart := rfl

theorem refinedLocalFamily_covers (K : Set P)
    (hK : ∀ p ∈ K, ∃ i, p ∈ B.inner i) :
    ∀ p ∈ K, ∃ i, p ∈ (originalRefinedLocalFamily B R b hb hbuffer s).inner i := by
  intro p hp
  obtain ⟨i, hi⟩ := hK p hp
  obtain ⟨c, hc, hd⟩ := s.covers i (B.chart i p) (tensorLocalInner_mem B i hi)
  refine ⟨i, B.inner_subset i hi, mem_iUnion.mpr ⟨⟨c,hc⟩, ?_⟩⟩
  change dist (B.chart i p) c < 3*b/8
  linarith

theorem refinedLocalFamily_sampling_subset_original (i : ι) :
    tensorLocalSamplingCoordinates (originalRefinedLocalFamily B R b hb hbuffer s) i ⊆
      tensorLocalSamplingCoordinates B i := by
  intro y hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp hy
  obtain ⟨hzInner, hyball⟩ := mem_iUnion.mp hz
  have hzdom := hzInner.2.2
  change B.chart i ((B.chart i).symm z) ∈ localRefinedWorkingDomain B R b hb s i at hzdom
  rw [(B.chart i).right_inv hzInner.1] at hzdom
  obtain ⟨c, hc⟩ := mem_iUnion.mp hzdom
  exact mem_iUnion.mpr ⟨c.val, mem_iUnion.mpr ⟨s.center_inner i c.property, by
    have hc' : dist z c.val < 3*b/8 := hc
    have hy' : dist y z < b/8 := hyball
    change dist y c.val < B.buffer
    linarith [dist_triangle y z c.val]⟩⟩

include hbuffer in
theorem localRefinedWorkingCarrier_target (i : ι) :
    centerRawCarrier E (s.centers i) (b/8) ⊆ (B.chart i).target := by
  intro y hy
  obtain ⟨c, hc⟩ := mem_iUnion.mp hy
  apply tensorLocalSampling_subset_target B i
  apply mem_iUnion.mpr
  refine ⟨c.val, mem_iUnion.mpr ⟨s.center_inner i c.property, ?_⟩⟩
  change dist y c.val < B.buffer
  have hc' : dist y c.val ≤ 2*(b/8) := hc
  linarith

theorem localRefinedWorkingCarrier_domain (i : ι) :
    centerRawCarrier E (s.centers i) (b/8) ⊆ localRefinedWorkingDomain B R b hb s i := by
  intro y hy
  obtain ⟨c, hc⟩ := mem_iUnion.mp hy
  apply mem_iUnion.mpr
  refine ⟨c, ?_⟩
  change dist y c.val < 3*b/8
  have hc' : dist y c.val ≤ 2*(b/8) := hc
  linarith

end GlobalEmbedding.Continuation.FaithfulCollars
