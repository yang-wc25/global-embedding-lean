import FaithfulCollars.FixedBallGeometry

/-!
# Internal working inners with the original charts, supports and norm sets

The old raw consumers need a neighborhood of the raw support, whereas the
paper's original inner ball is the smaller covering core.  The auxiliary
working atlas below is an INTERNAL geometric object.  It has the exact
original chart functions, count, supports and graph; it never replaces an
original norm domain.  Its sampling buffer is proved to lie inside the
original sampling buffer.  Thus the old strong raw interface can be filled
without changing the external given atlas or assuming its missing output.
-/

noncomputable section
open scoped ContDiff Manifold
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Metric

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M]

def originalWorkingAtlas (A : BufferedAtlas M E) (rho : ℝ)
    (g : OriginalFixedBallGeometry A rho) : BufferedAtlas M E where
  count := A.count
  chart := A.chart
  inner i := (A.chart i).source ∩ (A.chart i) ⁻¹' ball 0 (rho / 5)
  inner_open i := (A.chart i).isOpen_inter_preimage isOpen_ball
  inner_subset _ := inter_subset_left
  cover x := by
    obtain ⟨i, hi⟩ := A.cover x
    rw [g.inner_eq i] at hi
    exact ⟨i, hi.1, ball_subset_ball (by linarith [g.radius_pos]) hi.2⟩
  buffer := rho / 40
  buffer_pos := by linarith [g.radius_pos]
  buffered := by
    intro i x hx y hy
    apply g.target_buffer i
    have hx' : dist (A.chart i x) 0 < rho / 5 := hx.2
    have hy' : dist y (A.chart i x) < rho / 40 := hy
    change dist y 0 ≤ rho / 4
    linarith [dist_triangle y (A.chart i x) 0, g.radius_pos]
  support := A.support

variable (A : BufferedAtlas M E) (rho : ℝ) (g : OriginalFixedBallGeometry A rho)

theorem workingAtlas_chart_eq : (originalWorkingAtlas A rho g).chart = A.chart := rfl

theorem workingAtlas_support_eq : (originalWorkingAtlas A rho g).support = A.support := rfl

theorem workingAtlas_count_eq : (originalWorkingAtlas A rho g).count = A.count := rfl

theorem workingAtlas_degree_eq :
    (originalWorkingAtlas A rho g).supportDegree = A.supportDegree := rfl

theorem workingAtlas_inner_sampling (i : Fin A.count) (x : M)
    (hx : x ∈ (originalWorkingAtlas A rho g).inner i) :
    A.chart i x ∈ bufferedSamplingCoordinates A i := by
  apply g.ball_subset_original_sampling i
  exact ball_subset_ball (by linarith [g.radius_pos]) hx.2

theorem workingAtlas_sampling_subset_original (i : Fin A.count) :
    bufferedSamplingCoordinates (originalWorkingAtlas A rho g) i ⊆
      bufferedSamplingCoordinates A i := by
  intro y hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp hy
  obtain ⟨hzInner, hyball⟩ := mem_iUnion.mp hz
  have hzsmall : dist z 0 < rho / 5 := by
    have h := hzInner.2.2
    change A.chart i ((A.chart i).symm z) ∈ ball 0 (rho / 5) at h
    rw [(A.chart i).right_inv hzInner.1] at h
    exact h
  have hynear : dist y z < rho / 40 := hyball
  apply g.ball_subset_original_sampling i
  change dist y 0 < rho / 4
  linarith [dist_triangle y z 0, g.radius_pos]

variable [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem workingAtlas_smooth (hA : IsSmoothBufferedAtlas A) :
    IsSmoothBufferedAtlas (originalWorkingAtlas A rho g) :=
  ⟨hA.chart_mem, hA.support_subset⟩

end GlobalEmbedding.Continuation.FaithfulCollars
