import GlobalEmbedding.Offline.BufferedSamplingDomains
import GlobalEmbedding.Paper.IncrementsOriginalQualitativeAdmissibility
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Compactness from the same original bounded buffered atlas

A positive original buffer places the closure of each original inner
coordinate set inside the same sampling buffer, hence inside the same
chart target. Boundedness makes these coordinate closures compact; their
continuous inverse-chart images form a finite cover of the original source.

No source Hausdorff hypothesis, compactness of an observation set, changed
norm domain, replacement atlas, cutoff preparation or collar supply is used.
The original-data wrapper consumes the original source-inner inclusion and
the fixed numerical radius bound on the unchanged source norm domains.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Metric Manifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation.CollarCompletion

section Buffered
variable {E M : Type*} [NormedAddCommGroup E] [TopologicalSpace M]

/-- A limit of original inner coordinates is still in an original buffer
ball. The set containing it is the original sampling set, not a new norm set. -/
theorem original_inner_closure_subset_sampling
    (A : BufferedAtlas M E) (i : Fin A.count) :
    closure (bufferedInnerCoordinates A i) ⊆ bufferedSamplingCoordinates A i := by
  intro y hy
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hy A.buffer A.buffer_pos
  exact mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, hdist⟩⟩

/-- The original uniform outward buffer prevents an inner-coordinate
closure from reaching the boundary of its actual chart target. -/
theorem original_inner_closure_subset_target
    (A : BufferedAtlas M E) (i : Fin A.count) :
    closure (bufferedInnerCoordinates A i) ⊆ (A.chart i).target :=
  (original_inner_closure_subset_sampling A i).trans (bufferedSampling_subset_target A i)

/-- A finite original buffered atlas with bounded inner coordinate sets
already makes the source compact. The source need not be assumed Hausdorff. -/
theorem original_source_compact_of_bounded_inner_coordinates [ProperSpace E]
    (A : BufferedAtlas M E)
    (hBounded : ∀ i, Bornology.IsBounded (bufferedInnerCoordinates A i)) :
    CompactSpace M := by
  have hImage (i : Fin A.count) :
      IsCompact ((A.chart i).symm '' closure (bufferedInnerCoordinates A i)) :=
    (hBounded i).isCompact_closure.image_of_continuousOn
      ((A.chart i).continuousOn_symm.mono (original_inner_closure_subset_target A i))
  have hCover : (⋃ i, (A.chart i).symm '' closure (bufferedInnerCoordinates A i)) =
      (univ : Set M) := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := A.cover x
    apply mem_iUnion.mpr
    refine ⟨i, A.chart i x, subset_closure ?_, (A.chart i).left_inv (A.inner_subset i hi)⟩
    exact bufferedInnerCoordinates_mem A i hi
  exact ⟨hCover ▸ isCompact_iUnion hImage⟩

/-- In particular, a numerical upper radius for the same original inner
coordinates supplies compactness. No positivity of that upper bound is added. -/
theorem original_source_compact_of_inner_radius [ProperSpace E]
    (A : BufferedAtlas M E) (R : ℝ)
    (hRadius : ∀ i y, y ∈ bufferedInnerCoordinates A i → ‖y‖ ≤ R) :
    CompactSpace M := by
  apply original_source_compact_of_bounded_inner_coordinates A
  intro i
  have hBall : Bornology.IsBounded (Metric.closedBall (0 : E) R) := Metric.isBounded_closedBall
  apply hBall.subset
  intro y hy
  simpa only [Metric.mem_closedBall, dist_zero_right] using hRadius i y hy

/-- The unchanged original source norm domains only need to contain the
original inner points and have the original numerical upper radius. Their
closures, compactness or equality with chart targets are not assumed. -/
theorem original_source_compact_of_original_domain_radius [ProperSpace E]
    (A : BufferedAtlas M E) (Omega : Fin A.count → Set E)
    (hInner : ∀ i x, x ∈ A.inner i → A.chart i x ∈ Omega i)
    (R : ℝ) (hRadius : ∀ i y, y ∈ Omega i → ‖y‖ ≤ R) :
    CompactSpace M := by
  apply original_source_compact_of_inner_radius A R
  intro i y hy
  apply hRadius i y
  have h := hInner i ((A.chart i).symm y) hy.2
  simpa only [(A.chart i).right_inv hy.1] using h

/-- An existing original sampling inclusion is another direct entrance to
the same result; the observation domains themselves remain untouched. -/
theorem original_source_compact_of_sampling_radius [ProperSpace E]
    (A : BufferedAtlas M E) (Omega : Fin A.count → Set E)
    (hSampling : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (R : ℝ) (hRadius : ∀ i y, y ∈ Omega i → ‖y‖ ≤ R) :
    CompactSpace M := by
  apply original_source_compact_of_inner_radius A R
  intro i y hy
  exact hRadius i y (hSampling i (bufferedInner_subset_sampling A i hy))

end Buffered

section OriginalData
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- The original datum's actual source-inner inclusion and fixed source
coordinate-radius budget manufacture the source compactness internally.
No assumption about compactness of Omega, Q or the whole parameter space
is present; all original data fields are retained literally. -/
theorem original_data_source_compact_of_source_radius
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (R : ℝ)
    (hRadius : ∀ i y, y ∈ Data.sourceNormDomain i → ‖y‖ ≤ R) :
    CompactSpace M :=
  original_source_compact_of_original_domain_radius Data.atlas Data.sourceNormDomain
    hd.source_inner_norm R hRadius

end OriginalData
end GlobalEmbedding.Continuation.CollarCompletion

#print axioms GlobalEmbedding.Continuation.CollarCompletion.original_inner_closure_subset_sampling
#print axioms GlobalEmbedding.Continuation.CollarCompletion.original_source_compact_of_bounded_inner_coordinates
#print axioms GlobalEmbedding.Continuation.CollarCompletion.original_source_compact_of_original_domain_radius
#print axioms GlobalEmbedding.Continuation.CollarCompletion.original_data_source_compact_of_source_radius
