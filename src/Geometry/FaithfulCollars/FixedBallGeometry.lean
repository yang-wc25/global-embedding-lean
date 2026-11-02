import GlobalEmbedding.Paper.BufferedAtlas
import GlobalEmbedding.Offline.BufferedSamplingDomains

/-!
# The geometric content of the original fixed buffered balls

Source: `main.tex` 591 (fixed buffered coordinate radii), 698 (covering
bumps and enlarged supports), 816 (fixed buffered y-balls).  This is a
parallel faithful interface: it adds no desired raw function, derivative
estimate, or repair conclusion to the inputs.  The bare `BufferedAtlas`
record does not imply these geometric facts; its independently specified
supports do not even have to cover the source.  No old definition is changed.

The exact original charts, inners, enlarged supports and sampling sets are
retained.  The fractions are the fixed radii already used by the accepted
initialization construction: inner radius rho/10, raw support 3*rho/20,
enlarged radius rho/4.  They do not force raw support into the inner ball.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Metric

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M]

/-- Pure fixed-ball geometry, on the unchanged original atlas.  The core
cover is the old `A.cover`; `inner_eq` identifies its actual fixed balls.
The `target_buffer` is closed only for the small enlarged ball; the original
chart target and original norm domain need not be compact. -/
structure OriginalFixedBallGeometry (A : BufferedAtlas M E) (rho : ℝ) : Prop where
  radius_pos : 0 < rho
  inner_eq : ∀ i, A.inner i =
    (A.chart i).source ∩ (A.chart i) ⁻¹' ball 0 (rho / 10)
  target_buffer : ∀ i, closedBall (0 : E) (rho / 4) ⊆ (A.chart i).target
  enlarged_support : ∀ i,
    (A.chart i).source ∩ (A.chart i) ⁻¹' closedBall 0 (rho / 4) ⊆ A.support i
  buffer_lower : rho / 4 ≤ A.buffer

variable {A : BufferedAtlas M E} {rho : ℝ} (g : OriginalFixedBallGeometry A rho)

include g

theorem OriginalFixedBallGeometry.zero_mem_target (i : Fin A.count) :
    (0 : E) ∈ (A.chart i).target :=
  g.target_buffer i (mem_closedBall_self (by linarith [g.radius_pos]))

theorem OriginalFixedBallGeometry.zero_mem_inner_coordinates (i : Fin A.count) :
    (0 : E) ∈ bufferedInnerCoordinates A i := by
  refine ⟨g.zero_mem_target i, ?_⟩
  rw [g.inner_eq i]
  refine ⟨(A.chart i).map_target (g.zero_mem_target i), ?_⟩
  change A.chart i ((A.chart i).symm 0) ∈ ball 0 (rho / 10)
  rw [(A.chart i).right_inv (g.zero_mem_target i)]
  exact mem_ball_self (by linarith [g.radius_pos])

/-- A quantitative collar contained in the SAME original sampling set. -/
theorem OriginalFixedBallGeometry.ball_subset_original_sampling (i : Fin A.count) :
    ball (0 : E) (rho / 4) ⊆ bufferedSamplingCoordinates A i := by
  intro y hy
  refine mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨g.zero_mem_inner_coordinates i, ?_⟩⟩
  exact ball_subset_ball g.buffer_lower hy

/-- The smaller closed carrier is inside the original enlarged support;
this records actual support geometry rather than a requested output bound. -/
theorem OriginalFixedBallGeometry.small_carrier_support (i : Fin A.count)
    {x : M} (hx : x ∈ (A.chart i).source)
    (hy : A.chart i x ∈ closedBall 0 (3 * rho / 20)) : x ∈ A.support i := by
  exact g.enlarged_support i ⟨hx,
    closedBall_subset_closedBall (by linarith [g.radius_pos]) hy⟩

end GlobalEmbedding.Continuation.FaithfulCollars
