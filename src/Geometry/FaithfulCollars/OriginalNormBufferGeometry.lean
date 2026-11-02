import FaithfulCollars.ParameterRawFromCover
import FaithfulCollars.LocalRawPreparation

/-!
# Primitive buffered norm-cover geometry for the original raw supplier

Source: `main.tex` 234 (norms on a finite buffered atlas), 591 (fixed
buffered coordinate radii and enlarged-support degree), and 698--700
(covering bumps and localized smoothing on buffers).

The old native domain record only places the source inner in its norm
domain and covers the parameter set by arbitrary norm pieces.  It does
not encode a uniform collar in those same norm domains.  The structures
here record that missing GEOMETRIC information with literal coordinate
balls.  They contain no raw function, partition, collar family, output
derivative estimate or correction.  Both original norm domains remain
unchanged.  A smaller internal buffer need not fill the entire old buffer.

The centered-ball instances below follow from the already constructed
fixed-ball geometry and its literal larger norm balls.  No assertion is
made that arbitrary sets satisfying the old weak cover provide these
fixed radii.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M]

/-- Original geometry at one prescribed norm buffer.  The enlarged
support condition is a neighborhood relation between given chart sets. -/
structure OriginalSourceNormBuffer
    (A : BufferedAtlas M E) (Omega : Fin A.count → Set E) (R b : ℝ) : Prop where
  radius_pos : 0 < b
  chart_buffer : b ≤ A.buffer
  norm_target : ∀ i, Omega i ⊆ (A.chart i).target
  norm_radius : ∀ i y, y ∈ Omega i → ‖y‖ ≤ R
  norm_buffer : ∀ i x, x ∈ A.inner i → ball (A.chart i x) b ⊆ Omega i
  enlarged_buffer : OriginalBufferedEnlargedSupports A b

/-- Only the auxiliary buffer is reduced.  Every original coordinate,
inner, enlarged support and index is retained literally. -/
def originalNormBufferedAtlas (A : BufferedAtlas M E) (b : ℝ)
    (hb : 0 < b) (hbuffer : b ≤ A.buffer) : BufferedAtlas M E :=
  { A with
    buffer := b
    buffer_pos := hb
    buffered := fun i x hx => (ball_subset_ball hbuffer).trans (A.buffered i x hx) }

theorem originalNormBufferedAtlas_fields
    (A : BufferedAtlas M E) (b : ℝ) (hb : 0 < b) (hbuffer : b ≤ A.buffer) :
    (originalNormBufferedAtlas A b hb hbuffer).chart = A.chart ∧
    (originalNormBufferedAtlas A b hb hbuffer).inner = A.inner ∧
    (originalNormBufferedAtlas A b hb hbuffer).support = A.support ∧
    (originalNormBufferedAtlas A b hb hbuffer).supportDegree = A.supportDegree :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem OriginalSourceNormBuffer.original_sampling
    {A : BufferedAtlas M E} {Omega : Fin A.count → Set E} {R b : ℝ}
    (g : OriginalSourceNormBuffer A Omega R b) (i : Fin A.count) :
    bufferedSamplingCoordinates
      (originalNormBufferedAtlas A b g.radius_pos g.chart_buffer) i ⊆ Omega i := by
  intro y hy
  obtain ⟨c, hc⟩ := mem_iUnion.mp hy
  obtain ⟨hcinner, hyc⟩ := mem_iUnion.mp hc
  have h := g.norm_buffer i ((A.chart i).symm c) hcinner.2
  rw [(A.chart i).right_inv hcinner.1] at h
  exact h hyc

theorem OriginalSourceNormBuffer.inner_original_norm
    {A : BufferedAtlas M E} {Omega : Fin A.count → Set E} {R b : ℝ}
    (g : OriginalSourceNormBuffer A Omega R b) (i : Fin A.count) {x : M}
    (hx : x ∈ A.inner i) : A.chart i x ∈ Omega i :=
  g.norm_buffer i x hx (mem_ball_self g.radius_pos)

variable {F P ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace P]

/-- A local covering contract on the prescribed parameter set.  No cover
of the rest of the parameter manifold and no compactness of `Q` is used. -/
structure OriginalParameterNormBuffer
    (chart : ι → OpenPartialHomeomorph P F) (Q : ι → Set F)
    (W : ι → Set P) (K : Set P) (R b : ℝ) : Prop where
  radius_pos : 0 < b
  norm_target : ∀ i, Q i ⊆ (chart i).target
  norm_radius : ∀ i y, y ∈ Q i → ‖y‖ ≤ R
  cover : ∀ p ∈ K, ∃ i, p ∈ (chart i).source ∧
    ball (chart i p) b ⊆ Q i ∩ (chart i).symm ⁻¹' W i

theorem OriginalParameterNormBuffer.original_interior_cover
    {chart : ι → OpenPartialHomeomorph P F} {Q : ι → Set F}
    {W : ι → Set P} {K : Set P} {R b : ℝ}
    (g : OriginalParameterNormBuffer chart Q W K R b) :
    ∀ p ∈ K, ∃ i, p ∈ (chart i).source ∧ chart i p ∈ interior (Q i) := by
  intro p hp
  obtain ⟨i, hi, hball⟩ := g.cover p hp
  refine ⟨i, hi, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Metric.mem_nhds_iff.mpr ⟨b, g.radius_pos, hball.trans inter_subset_left⟩

theorem OriginalParameterNormBuffer.safe_ball_cover
    {chart : ι → OpenPartialHomeomorph P F} {Q : ι → Set F}
    {W : ι → Set P} {K : Set P} {R b : ℝ}
    (g : OriginalParameterNormBuffer chart Q W K R b) :
    OriginalParameterBallCover chart (originalParameterSafeCoordinates chart Q W) K b :=
  g.cover

/-- The accepted fixed-ball source geometry realizes this primitive
contract with buffer `rho/10`; only the original larger norm ball is read. -/
theorem originalSourceNormBuffer_of_fixed_balls
    (A : BufferedAtlas M E) (Omega : Fin A.count → Set E) (rho R : ℝ)
    (g : OriginalFixedBallGeometry A rho)
    (hTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hRadius : ∀ i y, y ∈ Omega i → ‖y‖ ≤ R)
    (hNormBall : ∀ i, ball (0 : E) (rho/4) ⊆ Omega i) :
    OriginalSourceNormBuffer A Omega R (rho/10) := by
  refine ⟨by linarith [g.radius_pos], (by linarith [g.buffer_lower, g.radius_pos]),
    hTarget, hRadius, ?_, ?_⟩
  · intro i x hx y hy
    rw [g.inner_eq i] at hx
    apply hNormBall i
    have hxsmall : dist (A.chart i x) 0 < rho/10 := hx.2
    change dist y (A.chart i x) < rho/10 at hy
    change dist y 0 < rho/4
    linarith [dist_triangle y (A.chart i x) 0, g.radius_pos]
  · intro i x hx hnear
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

/-- Parameter fixed balls likewise produce a safe inward norm/support
buffer from the actual core cover; the raw family is not an input. -/
theorem originalParameterNormBuffer_of_fixed_balls
    (chart : ι → OpenPartialHomeomorph P F) (Q : ι → Set F)
    (W : ι → Set P) (K : Set P) (rho R : ℝ)
    (g : OriginalLocalFixedBallGeometry chart K rho)
    (hTarget : ∀ i, Q i ⊆ (chart i).target)
    (hRadius : ∀ i y, y ∈ Q i → ‖y‖ ≤ R)
    (hNormBall : ∀ i, ball (0 : F) (rho/4) ⊆ Q i)
    (hSupport : ∀ i, (chart i).source ∩ (chart i) ⁻¹' closedBall 0 (rho/4) ⊆ W i) :
    OriginalParameterNormBuffer chart Q W K R (rho/10) := by
  refine ⟨by linarith [g.radius_pos], hTarget, hRadius, ?_⟩
  intro p hp
  obtain ⟨i, hi, hsmall⟩ := g.core_cover p hp
  refine ⟨i, hi, ?_⟩
  intro y hy
  have hyball : y ∈ ball (0 : F) (rho/4) := by
    have hx : dist (chart i p) 0 < rho/10 := hsmall
    have hy' : dist y (chart i p) < rho/10 := hy
    change dist y 0 < rho/4
    linarith [dist_triangle y (chart i p) 0, g.radius_pos]
  have hytarget := g.target_buffer i (ball_subset_closedBall hyball)
  refine ⟨hNormBall i hyball, hSupport i ⟨(chart i).map_target hytarget, ?_⟩⟩
  change chart i ((chart i).symm y) ∈ closedBall 0 (rho/4)
  rw [(chart i).right_inv hytarget]
  exact ball_subset_closedBall hyball

end GlobalEmbedding.Continuation.FaithfulCollars
