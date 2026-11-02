import FaithfulCollars.SamplingNormalization

/-!
# Actual convex collars in the original norm domains

For every original chart the carrier is the closed ball of radius 3*rho/20
and the differentiation collar is the open ball of radius rho/5.  Their
common inward radius is rho/40.  These are constructed sets with the
ORIGINAL coordinates, support labels, and sampling domains.  There is one
such initial collar per original chart.  None depends on a reference map,
phase, correction, observation order, or desired output estimate.

The old collars' `domain_inner` condition is replaced here by the exact
conditions consumers need: domain in the original norm domain and actual
cutoff carrier in the original enlarged support.  The covering inner set
is left literally unchanged; the collar need not be inside that smaller set.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def originalBallCollarDomain (rho : ℝ) : Set E := ball 0 (rho / 5)

def originalBallCollarCarrier (rho : ℝ) : Set E := closedBall 0 (3 * rho / 20)

theorem originalBallCollar_buffer {rho : ℝ} (hrho : 0 < rho)
    {y : E} (hy : y ∈ originalBallCollarCarrier rho) :
    ball y (rho / 40) ⊆ originalBallCollarDomain rho := by
  intro z hz
  change dist y 0 ≤ 3 * rho / 20 at hy
  change dist z y < rho / 40 at hz
  change dist z 0 < rho / 5
  linarith [dist_triangle z y 0]

variable {A : BufferedAtlas M E} {rho : ℝ} (g : OriginalFixedBallGeometry A rho)

include g

theorem originalBallCollar_original_sampling (i : Fin A.count) :
    originalBallCollarDomain (E := E) rho ⊆ bufferedSamplingCoordinates A i := by
  exact (ball_subset_ball (by linarith [g.radius_pos])).trans (g.ball_subset_original_sampling i)

theorem originalBallCollar_original_target (i : Fin A.count) :
    originalBallCollarDomain (E := E) rho ⊆ (A.chart i).target :=
  (originalBallCollar_original_sampling g i).trans (bufferedSampling_subset_target A i)

theorem originalBallCollar_original_support (i : Fin A.count) :
    MapsTo (A.chart i).symm (originalBallCollarDomain (E := E) rho) (A.support i) := by
  intro y hy
  have ht := originalBallCollar_original_target g i hy
  apply g.enlarged_support i
  refine ⟨(A.chart i).map_target ht, ?_⟩
  change A.chart i ((A.chart i).symm y) ∈ closedBall 0 (rho / 4)
  rw [(A.chart i).right_inv ht]
  exact ball_subset_closedBall ((ball_subset_ball (by linarith [g.radius_pos])) hy)

theorem originalBallCutoff_original_carrier (i : Fin A.count) :
    tsupport (originalBallCutoff A rho i) ⊆
      (A.chart i).source ∩ (A.chart i) ⁻¹' originalBallCollarCarrier rho := by
  exact (originalBallCutoff_support A rho i).trans (originalBallRaw_compact_support g i).2

/-- Source norm-domain membership comes from the original sampling contract;
it is not obtained by silently replacing Omega by a smaller compact domain. -/
theorem originalBallCollar_original_norm_domain
    (Omega : Fin A.count → Set E)
    (hOmega : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) (i : Fin A.count) :
    originalBallCollarDomain (E := E) rho ⊆ Omega i :=
  (originalBallCollar_original_sampling g i).trans (hOmega i)

/-- All source-collar facts are actual outputs of the fixed original balls.
The open and closed sets below are explicit; no collar field is a premise. -/
theorem originalBallCollars_construct
    (Omega : Fin A.count → Set E)
    (hOmega : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) :
    0 < rho / 40 ∧
    IsOpen (originalBallCollarDomain (E := E) rho) ∧
    Convex ℝ (originalBallCollarDomain (E := E) rho) ∧
    IsCompact (originalBallCollarCarrier (E := E) rho) ∧
    (∀ y ∈ originalBallCollarCarrier (E := E) rho,
      ball y (rho / 40) ⊆ originalBallCollarDomain rho) ∧
    (∀ i, originalBallCollarDomain (E := E) rho ⊆ Omega i) ∧
    (∀ i, originalBallCollarDomain (E := E) rho ⊆ (A.chart i).target) ∧
    (∀ i, MapsTo (A.chart i).symm (originalBallCollarDomain (E := E) rho) (A.support i)) ∧
    (∀ i, tsupport (originalBallCutoff A rho i) ⊆
      (A.chart i).source ∩ (A.chart i) ⁻¹' originalBallCollarCarrier rho) := by
  exact ⟨by linarith [g.radius_pos], isOpen_ball, convex_ball _ _, isCompact_closedBall _ _,
    fun _ hy => originalBallCollar_buffer g.radius_pos hy,
    originalBallCollar_original_norm_domain g Omega hOmega,
    originalBallCollar_original_target g, originalBallCollar_original_support g,
    originalBallCutoff_original_carrier g⟩

end GlobalEmbedding.Continuation.FaithfulCollars
