import GlobalEmbedding.Offline.BufferedSamplingDomains
import Probes.ActualRefinementTotalCount
import Probes.Round4RefinementSquareCutoffs

/-!
# Convex source collars from the original buffered coordinate domains

Source: `setup:uniform` and the localization in the proof of `thm:repair`.
The original atlas, its chart maps, its sampling domains, and its norm domains
are parameters of this construction and are never replaced. Only a finite
family of centers inside each original inner coordinate set is constructed.
The total number per chart is chosen from the fixed radius budget before the
atlas. Every collar lies in the original sampling set, with the same buffer
fraction for every chart. No convexity of an entire original chart is assumed.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The uniform total piece bound uses only the original coordinate radius
and buffer budget. It does not depend on chart count or a reference map. -/
def sourceCollarNovPieceBound (R b : ℝ) (hb : 0 < b) : ℕ :=
  Classical.choose (actual_exists_uniform_total_refinement_bound E R (b / 8)
    (by positivity))

variable {E} {M : Type*} [TopologicalSpace M]

/-- Actual finitely many collars over unchanged original chart indices.
Each carrier is `closedBall c (b/4)` and its convex open domain is
`ball c (3*b/8)`. This data is constructed below from the original buffer;
it is not an extra input to that construction. -/
structure SourceCollarNovFamily (A : BufferedAtlas M E)
    (Omega : Fin A.count → Set E) (R b : ℝ) (hb : 0 < b) where
  centers : Fin A.count → Finset E
  center_inner : ∀ i, (↑(centers i) : Set E) ⊆ bufferedInnerCoordinates A i
  separated : ∀ i, ∀ a ∈ centers i, ∀ c ∈ centers i,
    a ≠ c → b / 8 ≤ dist a c
  count_le : ∀ i, (centers i).card ≤ sourceCollarNovPieceBound E R b hb
  covers : ∀ i y, y ∈ bufferedInnerCoordinates A i →
    ∃ c ∈ centers i, dist y c ≤ b / 8
  domain_sample : ∀ i c, c ∈ centers i →
    ball c (3 * b / 8) ⊆ Omega i
  domain_target : ∀ i c, c ∈ centers i →
    ball c (3 * b / 8) ⊆ (A.chart i).target
  carrier_buffer : ∀ i c, c ∈ centers i → ∀ y ∈ closedBall c (b / 4),
    ball y (b / 8) ⊆ ball c (3 * b / 8)
  center_bound : ∀ i c, c ∈ centers i → ‖c‖ ≤ R

/-- Uniform source-collar production from the ORIGINAL buffered atlas.
`R` and `b` are fixed radius bounds, the original norm sets contain the
original sampling sets, and the latter are bounded by `R`. Nothing about a
desired correction, any phase, or any derivative of an output is assumed.
This also covers empty atlases and zero-dimensional coordinate models. -/
theorem sourceCollarNov_construct (R b : ℝ) (hb : 0 < b)
    (A : BufferedAtlas M E) (Omega : Fin A.count → Set E)
    (hbuffer : b ≤ A.buffer)
    (hSampling : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hRadius : ∀ i y, y ∈ Omega i → ‖y‖ ≤ R) :
    Nonempty (SourceCollarNovFamily A Omega R b hb) := by
  classical
  have hr : 0 < b / 8 := by positivity
  have hInnerBall (i : Fin A.count) :
      bufferedInnerCoordinates A i ⊆ closedBall (0 : E) R := by
    intro y hy
    simpa only [mem_closedBall, dist_zero_right] using
      hRadius i y (hSampling i (bufferedInner_subset_sampling A i hy))
  have hCenters (i : Fin A.count) := actual_exists_finite_bounded_refinement
    (bufferedInnerCoordinates A i)
    ((isCompact_closedBall (0 : E) R).totallyBounded.subset (hInnerBall i))
    (b / 8) hr
  choose centers hSubset hSeparated hCover hLocal using hCenters
  have hDomain (i : Fin A.count) (c : E) (hc : c ∈ centers i) :
      ball c (3 * b / 8) ⊆ bufferedSamplingCoordinates A i := by
    intro y hy
    apply mem_iUnion.mpr
    refine ⟨c, mem_iUnion.mpr ⟨hSubset i hc, ?_⟩⟩
    exact (ball_subset_ball (by linarith : 3 * b / 8 ≤ A.buffer)) hy
  refine ⟨{
    centers := centers
    center_inner := hSubset
    separated := hSeparated
    count_le := ?_
    covers := hCover
    domain_sample := fun i c hc => (hDomain i c hc).trans (hSampling i)
    domain_target := fun i c hc =>
      (hDomain i c hc).trans (bufferedSampling_subset_target A i)
    carrier_buffer := ?_
    center_bound := ?_ }⟩
  · intro i
    apply Classical.choose_spec (actual_exists_uniform_total_refinement_bound E R (b / 8) hr)
      (centers i) 0
    · intro c hc
      exact hInnerBall i (hSubset i hc)
    · exact hSeparated i
  · intro i c hc y hy z hz
    have hy' : dist y c ≤ b / 4 := hy
    have hz' : dist z y < b / 8 := hz
    change dist z c < 3 * b / 8
    have ht := dist_triangle z y c
    linarith
  · intro i c hc
    exact hRadius i c (hSampling i (bufferedInner_subset_sampling A i (hSubset i hc)))

namespace SourceCollarNovFamily

variable {A : BufferedAtlas M E} {Omega : Fin A.count → Set E} {R b : ℝ}
  {hb : 0 < b} (s : SourceCollarNovFamily A Omega R b hb)

/-- The actual open convex collar, in the unchanged original coordinates. -/
def domain (i : Fin A.count) (c : s.centers i) : Set E := ball c.val (3 * b / 8)

/-- The actual compact carrier, in the unchanged original coordinates. -/
def carrier (i : Fin A.count) (c : s.centers i) : Set E := closedBall c.val (b / 4)

theorem domain_open (i : Fin A.count) (c : s.centers i) : IsOpen (s.domain i c) :=
  isOpen_ball

theorem domain_convex (i : Fin A.count) (c : s.centers i) : Convex ℝ (s.domain i c) :=
  convex_ball _ _

theorem carrier_compact (i : Fin A.count) (c : s.centers i) : IsCompact (s.carrier i c) :=
  isCompact_closedBall _ _

end SourceCollarNovFamily
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNov_construct
