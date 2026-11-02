import FaithfulCollars.WorkingAtlas
import Smoothing.TensorLocalModelDomains

/-!
# A working parameter family on the given compact evaluation set

This local version does not suppose that the parameter manifold is compact,
or that finitely many parameter charts cover it.  The only cover is the
original geometric cover of the stated set K by small coordinate balls.
The chart functions and original parameter norm pieces are never changed.

The fixed-ball conditions formalize the buffered coordinate radii of
`setup:uniform` (main.tex 591), with the norm convention in main.tex 234.
They are not consequences of the weaker arbitrary-set `parameter_cover`
field of `IncrementsOriginalDomainConditions`; that missing distinction is
recorded explicitly instead of adding a raw partition as a hypothesis.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Metric
open scoped ContDiff Manifold

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {ι E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace P]

/-- Pure original coordinate geometry.  `core_cover` asserts a covering
relation between the given points and the given charts, not a property of
any constructed raw or normalized function. -/
structure OriginalLocalFixedBallGeometry
    (chart : ι → OpenPartialHomeomorph P E) (K : Set P) (rho : ℝ) : Prop where
  radius_pos : 0 < rho
  target_buffer : ∀ i, closedBall (0 : E) (rho / 4) ⊆ (chart i).target
  core_cover : ∀ p ∈ K, ∃ i, p ∈ (chart i).source ∩ (chart i) ⁻¹' ball 0 (rho / 10)

/-- One internal local working family, with exactly the original chart
functions and no claim to cover points outside K. -/
def originalWorkingLocalFamily
    (chart : ι → OpenPartialHomeomorph P E) (K : Set P) (rho : ℝ)
    (g : OriginalLocalFixedBallGeometry chart K rho) : TensorBufferedChartFamily ι P E where
  chart := chart
  inner i := (chart i).source ∩ (chart i) ⁻¹' ball 0 (rho / 5)
  inner_open i := (chart i).isOpen_inter_preimage isOpen_ball
  inner_subset _ := inter_subset_left
  buffer := rho / 40
  buffer_pos := by linarith [g.radius_pos]
  buffered := by
    intro i p hp y hy
    apply g.target_buffer i
    have hp' : dist (chart i p) 0 < rho / 5 := hp.2
    have hy' : dist y (chart i p) < rho / 40 := hy
    change dist y 0 ≤ rho / 4
    linarith [dist_triangle y (chart i p) 0, g.radius_pos]

theorem workingLocalFamily_chart_eq
    (chart : ι → OpenPartialHomeomorph P E) (K : Set P) (rho : ℝ)
    (g : OriginalLocalFixedBallGeometry chart K rho) :
    (originalWorkingLocalFamily chart K rho g).chart = chart := rfl

theorem workingLocalFamily_covers
    (chart : ι → OpenPartialHomeomorph P E) (K : Set P) (rho : ℝ)
    (g : OriginalLocalFixedBallGeometry chart K rho) :
    ∀ p ∈ K, ∃ i, p ∈ (originalWorkingLocalFamily chart K rho g).inner i := by
  intro p hp
  obtain ⟨i, hi⟩ := g.core_cover p hp
  exact ⟨i, hi.1, ball_subset_ball (by linarith [g.radius_pos]) hi.2⟩

variable [Fintype ι]

theorem workingLocalFamily_sampling_subset_ball
    (chart : ι → OpenPartialHomeomorph P E) (K : Set P) (rho : ℝ)
    (g : OriginalLocalFixedBallGeometry chart K rho) (i : ι) :
    tensorLocalSamplingCoordinates (originalWorkingLocalFamily chart K rho g) i ⊆
      ball 0 (rho / 4) := by
  intro y hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp hy
  obtain ⟨hzInner, hyball⟩ := mem_iUnion.mp hz
  have hzsmall : dist z 0 < rho / 5 := by
    have h := hzInner.2.2
    change chart i ((chart i).symm z) ∈ ball 0 (rho / 5) at h
    rw [(chart i).right_inv hzInner.1] at h
    exact h
  have hynear : dist y z < rho / 40 := hyball
  change dist y 0 < rho / 4
  linarith [dist_triangle y z 0, g.radius_pos]

/-- The original Q is unchanged.  This uses the original buffered-ball
sampling contract; it never replaces Q with a compact or smaller set. -/
theorem workingLocalFamily_sampling_in_original_domain
    (chart : ι → OpenPartialHomeomorph P E) (K : Set P) (rho : ℝ)
    (g : OriginalLocalFixedBallGeometry chart K rho)
    (Q : ι → Set E) (hQ : ∀ i, ball 0 (rho / 4) ⊆ Q i) (i : ι) :
    tensorLocalSamplingCoordinates (originalWorkingLocalFamily chart K rho g) i ⊆ Q i :=
  (workingLocalFamily_sampling_subset_ball chart K rho g i).trans (hQ i)

/-- A previously given whole-source fixed-ball atlas gives the local
geometry on any requested set, but the local producer itself never needs
a whole-parameter atlas. -/
theorem originalLocalGeometry_of_fixedBallAtlas
    (A : BufferedAtlas P E) (rho : ℝ) (g : OriginalFixedBallGeometry A rho) (K : Set P) :
    OriginalLocalFixedBallGeometry A.chart K rho := by
  refine ⟨g.radius_pos, g.target_buffer, ?_⟩
  intro p _
  obtain ⟨i, hi⟩ := A.cover p
  exact ⟨i, by rwa [← g.inner_eq i]⟩

end GlobalEmbedding.Continuation.FaithfulCollars
