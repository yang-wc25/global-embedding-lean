import GlobalEmbedding.Offline.ScaledChartBumps
import Probes.ActualRefinementPartitionJets

/-!
# Actual compact chart cutoffs extended by zero

The local refinement cutoff is pulled back through its original chart and
set equal to zero off the chart source.  Compact support in the genuine
target produces global smoothness, compact absolute support, and the exact
all-order coordinate jets.  Arbitrary off-source values of a partial chart
are never used to assert smoothness.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def repairReferenceChartCutoff (q : OpenPartialHomeomorph M F) (eta : F → ℝ) : M → ℝ :=
  q.source.indicator (eta ∘ q)

theorem repair_reference_chart_cutoff_on_source
    (q : OpenPartialHomeomorph M F) (eta : F → ℝ) {x : M} (hx : x ∈ q.source) :
    repairReferenceChartCutoff q eta x = eta (q x) :=
  indicator_of_mem hx _

theorem repair_reference_chart_cutoff_off_source
    (q : OpenPartialHomeomorph M F) (eta : F → ℝ) {x : M} (hx : x ∉ q.source) :
    repairReferenceChartCutoff q eta x = 0 :=
  indicator_of_notMem hx _

theorem repair_reference_chart_cutoff_support
    (q : OpenPartialHomeomorph M F) (eta : F → ℝ)
    (hCompact : IsCompact (tsupport eta)) (hTarget : tsupport eta ⊆ q.target) :
    HasCompactSupport (repairReferenceChartCutoff q eta) ∧
      tsupport (repairReferenceChartCutoff q eta) ⊆
        q.source ∩ q ⁻¹' tsupport eta := by
  have hCarrier : IsCompact (q.symm '' tsupport eta) :=
    hCompact.image_of_continuousOn (q.continuousOn_symm.mono hTarget)
  have hSupport : support (repairReferenceChartCutoff q eta) ⊆ q.symm '' tsupport eta := by
    intro x hx
    have hsource : x ∈ q.source := by
      by_contra hn
      exact hx (repair_reference_chart_cutoff_off_source q eta hn)
    have heta : eta (q x) ≠ 0 := by
      change repairReferenceChartCutoff q eta x ≠ 0 at hx
      rwa [repair_reference_chart_cutoff_on_source q eta hsource] at hx
    exact ⟨q x, subset_tsupport eta heta, q.left_inv hsource⟩
  have hClosedSupport : tsupport (repairReferenceChartCutoff q eta) ⊆ q.symm '' tsupport eta :=
    closure_minimal hSupport hCarrier.isClosed
  refine ⟨hCarrier.of_isClosed_subset (isClosed_tsupport _) hClosedSupport, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hClosedSupport hx
  refine ⟨q.map_target (hTarget hy), ?_⟩
  change q (q.symm y) ∈ tsupport eta
  rwa [q.right_inv (hTarget hy)]

theorem repair_reference_chart_cutoff_smooth
    (I : ModelWithCorners ℝ E H) (q : OpenPartialHomeomorph M F) (eta : F → ℝ)
    (hq : ContMDiffOn I 𝓘(ℝ,F) ∞ q q.source) (hEta : ContDiff ℝ ∞ eta)
    (hCompact : IsCompact (tsupport eta)) (hTarget : tsupport eta ⊆ q.target) :
    ContMDiff I 𝓘(ℝ,ℝ) ∞ (repairReferenceChartCutoff q eta) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hsource := ((repair_reference_chart_cutoff_support q eta hCompact hTarget).2 hx).1
  have hcomp := hEta.contMDiff.contMDiffAt.comp x
    (hq.contMDiffAt (q.open_source.mem_nhds hsource))
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [q.open_source.mem_nhds hsource] with z hz
  exact repair_reference_chart_cutoff_on_source q eta hz

theorem repair_reference_chart_cutoff_coordinates
    (q : OpenPartialHomeomorph M F) (eta : F → ℝ) {y : F} (hy : y ∈ q.target) :
    repairReferenceChartCutoff q eta (q.symm y) = eta y := by
  rw [repair_reference_chart_cutoff_on_source q eta (q.map_target hy), q.right_inv hy]

theorem repair_reference_chart_cutoff_jets
    (q : OpenPartialHomeomorph M F) (eta : F → ℝ) (j : ℕ)
    {y : F} (hy : y ∈ q.target) :
    iteratedFDeriv ℝ j (repairReferenceChartCutoff q eta ∘ q.symm) y =
      iteratedFDeriv ℝ j eta y := by
  have heq : repairReferenceChartCutoff q eta ∘ q.symm =ᶠ[𝓝 y] eta := by
    filter_upwards [q.open_target.mem_nhds hy] with z hz
    exact repair_reference_chart_cutoff_coordinates q eta hz
  exact (heq.iteratedFDeriv ℝ j).eq_of_nhds

/-- The actual produced refinement bump is the local input; compact target
containment is the genuine factory containment and no global chart
composition is assumed smooth. -/
theorem repair_reference_refinement_cutoff_extension
    [FiniteDimensional ℝ F]
    (I : ModelWithCorners ℝ E H) (q : OpenPartialHomeomorph M F)
    (hq : ContMDiffOn I 𝓘(ℝ,F) ∞ q q.source)
    (s : Finset F) (r : ℝ) (hr : 0 < r) (c : F)
    (hTarget : tsupport (actualRefinementCutoff F s r c) ⊆ q.target) :
    let chi := repairReferenceChartCutoff q (actualRefinementCutoff F s r c)
    ContMDiff I 𝓘(ℝ,ℝ) ∞ chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ q.source ∩ q ⁻¹' tsupport (actualRefinementCutoff F s r c) ∧
      (∀ x ∈ q.source, chi x = actualRefinementCutoff F s r c (q x)) ∧
      ∀ j y, y ∈ q.target →
        iteratedFDeriv ℝ j (chi ∘ q.symm) y =
          iteratedFDeriv ℝ j (actualRefinementCutoff F s r c) y := by
  intro chi
  have hCompact : IsCompact (tsupport (actualRefinementCutoff F s r c)) :=
    (isCompact_closedBall c (2*r)).of_isClosed_subset (isClosed_tsupport _)
      (actualRefinementCutoff_tsupport F s r hr c)
  exact ⟨repair_reference_chart_cutoff_smooth I q _ hq
    (actualRefinementCutoff_contDiff F s r c) hCompact hTarget,
    (repair_reference_chart_cutoff_support q _ hCompact hTarget).1,
    (repair_reference_chart_cutoff_support q _ hCompact hTarget).2,
    fun _ hx => repair_reference_chart_cutoff_on_source q _ hx,
    fun j _ hy => repair_reference_chart_cutoff_jets q _ j hy⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_chart_cutoff_support
#print axioms GlobalEmbedding.Continuation.repair_reference_chart_cutoff_smooth
#print axioms GlobalEmbedding.Continuation.repair_reference_chart_cutoff_jets
#print axioms GlobalEmbedding.Continuation.repair_reference_refinement_cutoff_extension
