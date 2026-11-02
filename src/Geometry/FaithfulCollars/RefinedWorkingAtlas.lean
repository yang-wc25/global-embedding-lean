import FaithfulCollars.ChartCenterRaw
import FaithfulCollars.FixedBallGeometry
import Repair.SourceCollarNovFiniteCover

/-!
# General original buffered charts: internal working atlas

The centers are produced by the existing uniform finite-cover theorem from
the ORIGINAL bounded coordinate inners and their ORIGINAL outward buffer.
No original inner is required to be a ball, no center is required to be
zero, and no coordinate map is changed.  The auxiliary inner is the union
of the actual manufactured collar balls.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M]

/-- The geometric meaning of enlarged chart supports at the fixed buffer
scale. This condition contains no raw function or desired output estimate. -/
def OriginalBufferedEnlargedSupports (A : BufferedAtlas M E) (b : ℝ) : Prop :=
  ∀ i x, x ∈ (A.chart i).source →
    (∃ c ∈ bufferedInnerCoordinates A i, dist (A.chart i x) c ≤ b / 4) →
    x ∈ A.support i

variable (A : BufferedAtlas M E) (Omega : Fin A.count → Set E)
  (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ A.buffer)
  (s : SourceCollarNovFamily A Omega R b hb)

def refinedWorkingDomain (i : Fin A.count) : Set E :=
  ⋃ c : s.centers i, ball c.val (3*b/8)

theorem refinedWorkingDomain_open (i : Fin A.count) :
    IsOpen (refinedWorkingDomain A Omega R b hb s i) :=
  isOpen_iUnion fun _ => isOpen_ball

include hbuffer in
theorem refinedWorkingDomain_sampling (i : Fin A.count) :
    refinedWorkingDomain A Omega R b hb s i ⊆ bufferedSamplingCoordinates A i := by
  intro y hy
  obtain ⟨c, hc⟩ := mem_iUnion.mp hy
  exact mem_iUnion.mpr ⟨c.val, mem_iUnion.mpr ⟨s.center_inner i c.property,
    ball_subset_ball (by linarith) hc⟩⟩

def originalRefinedWorkingAtlas : BufferedAtlas M E where
  count := A.count
  chart := A.chart
  inner i := (A.chart i).source ∩ (A.chart i) ⁻¹' refinedWorkingDomain A Omega R b hb s i
  inner_open i := (A.chart i).isOpen_inter_preimage (refinedWorkingDomain_open A Omega R b hb s i)
  inner_subset _ := inter_subset_left
  cover x := by
    obtain ⟨i, hi⟩ := A.cover x
    have hy := bufferedInnerCoordinates_mem A i hi
    obtain ⟨c, hc, hyc⟩ := s.covers i (A.chart i x) hy
    refine ⟨i, A.inner_subset i hi, mem_iUnion.mpr ⟨⟨c, hc⟩, ?_⟩⟩
    change dist (A.chart i x) c < 3*b/8
    linarith
  buffer := b/8
  buffer_pos := by positivity
  buffered := by
    intro i x hx y hy
    obtain ⟨c, hc⟩ := mem_iUnion.mp hx.2
    apply bufferedSampling_subset_target A i
    apply mem_iUnion.mpr
    refine ⟨c.val, mem_iUnion.mpr ⟨s.center_inner i c.property, ?_⟩⟩
    have hc' : dist (A.chart i x) c.val < 3*b/8 := hc
    have hy' : dist y (A.chart i x) < b/8 := hy
    change dist y c.val < A.buffer
    linarith [dist_triangle y (A.chart i x) c.val]
  support := A.support

theorem refinedWorkingAtlas_chart_eq :
    (originalRefinedWorkingAtlas A Omega R b hb hbuffer s).chart = A.chart := rfl

theorem refinedWorkingAtlas_support_eq :
    (originalRefinedWorkingAtlas A Omega R b hb hbuffer s).support = A.support := rfl

theorem refinedWorkingAtlas_degree_eq :
    (originalRefinedWorkingAtlas A Omega R b hb hbuffer s).supportDegree = A.supportDegree := rfl

theorem refinedWorkingAtlas_inner_sampling (i : Fin A.count) (x : M)
    (hx : x ∈ (originalRefinedWorkingAtlas A Omega R b hb hbuffer s).inner i) :
    A.chart i x ∈ bufferedSamplingCoordinates A i :=
  refinedWorkingDomain_sampling A Omega R b hb hbuffer s i hx.2

theorem refinedWorkingAtlas_sampling_subset_original (i : Fin A.count) :
    bufferedSamplingCoordinates (originalRefinedWorkingAtlas A Omega R b hb hbuffer s) i ⊆
      bufferedSamplingCoordinates A i := by
  intro y hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp hy
  obtain ⟨hzInner, hyball⟩ := mem_iUnion.mp hz
  have hzdom := hzInner.2.2
  change A.chart i ((A.chart i).symm z) ∈ refinedWorkingDomain A Omega R b hb s i at hzdom
  rw [(A.chart i).right_inv hzInner.1] at hzdom
  obtain ⟨c, hc⟩ := mem_iUnion.mp hzdom
  exact mem_iUnion.mpr ⟨c.val, mem_iUnion.mpr ⟨s.center_inner i c.property, by
    have hc' : dist z c.val < 3*b/8 := hc
    have hy' : dist y z < b/8 := hyball
    change dist y c.val < A.buffer
    linarith [dist_triangle y z c.val]⟩⟩

theorem refinedWorkingCarrier_target (i : Fin A.count) :
    centerRawCarrier E (s.centers i) (b/8) ⊆ (A.chart i).target := by
  intro y hy
  obtain ⟨c, hc⟩ := mem_iUnion.mp hy
  apply s.domain_target i c.val c.property
  change dist y c.val < 3*b/8
  have hc' : dist y c.val ≤ 2*(b/8) := hc
  linarith

theorem refinedWorkingCarrier_domain (i : Fin A.count) :
    centerRawCarrier E (s.centers i) (b/8) ⊆ refinedWorkingDomain A Omega R b hb s i := by
  intro y hy
  obtain ⟨c, hc⟩ := mem_iUnion.mp hy
  apply mem_iUnion.mpr
  refine ⟨c, ?_⟩
  change dist y c.val < 3*b/8
  have hc' : dist y c.val ≤ 2*(b/8) := hc
  linarith

variable [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem refinedWorkingAtlas_smooth (hA : IsSmoothBufferedAtlas A) :
    IsSmoothBufferedAtlas (originalRefinedWorkingAtlas A Omega R b hb hbuffer s) :=
  ⟨hA.chart_mem, hA.support_subset⟩

omit [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The actual accepted centered-ball instance satisfies the more general
enlarged-support condition.  Thus the new condition does not exclude that
instance or assume a desired raw support statement. -/
theorem OriginalFixedBallGeometry.bufferedEnlargedSupports
    {rho : ℝ} (g : OriginalFixedBallGeometry A rho) (hbR : b ≤ rho/2) :
    OriginalBufferedEnlargedSupports A b := by
  intro i x hx hnear
  obtain ⟨c, hc, hxc⟩ := hnear
  have hcinner := hc.2
  rw [g.inner_eq i] at hcinner
  have hcsmall : dist c 0 < rho/10 := by
    have h := hcinner.2
    change A.chart i ((A.chart i).symm c) ∈ ball 0 (rho/10) at h
    rw [(A.chart i).right_inv hc.1] at h
    exact h
  apply g.enlarged_support i
  refine ⟨hx, ?_⟩
  change dist (A.chart i x) 0 ≤ rho/4
  linarith [dist_triangle (A.chart i x) c 0, g.radius_pos]

end GlobalEmbedding.Continuation.FaithfulCollars
