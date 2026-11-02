import Repair.SourceCollarNovParentPrepared
import Smoothing.TensorLocalPrepared

/-!
# Actual parent normalization jets in every original observer chart

The existing normalization producer is applied to the newly constructed
raw preparation. It supplies all mixed-chart derivatives from the original
B, T and enlarged-support degree D, before the original atlas or raw family
is chosen. Neither a normalized-cutoff derivative estimate nor a new overlap
budget is accepted as input.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem sourceCollarNovParent_local_count
    {A : BufferedAtlas M E} {B T : ℕ → ℝ} {D : ℕ}
    (R : TensorRawCutoffPreparation A B T D) (x : M) :
    (activeCutoffIndices (sourceCollarNovParent R) x).card ≤ D+1 :=
  activeCutoffIndices_card_le_enlarged_degree A.support (sourceCollarNovParent R)
    (fun i => (sourceCollarNovParent_original_support R i).trans (R.enlarged_support i)) D
    (fun i => (tensorSupportDegree_le_original A i).trans R.degree) x

/-- The same actually constructed parent is controlled in every original
observer, with constants independent of the number of charts. -/
theorem sourceCollarNov_parent_uniform_normalized_jets
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
        (R : TensorRawCutoffPreparation A B T D),
      ∀ p i j y, y ∈ (A.chart p).target →
        ‖iteratedFDeriv ℝ j (sourceCollarNovParent R i ∘ (A.chart p).symm) y‖ ≤ C j := by
  obtain ⟨C,hC,hProvider⟩ := exists_uniform_local_normalized_cutoff_provider (E := E) (X := M)
    (sourceCollarNovParentRawProfile B) T (sourceCollarNovParentRawProfile_nonneg B hB) hT (D+1)
  refine ⟨C,hC,?_⟩
  intro A hA R p i j y hy
  let R' := sourceCollarNovParentRawPreparation hA R hB
  have hCount (x : M) : (activeCutoffIndices R'.raw x).card ≤ D+1 :=
    activeCutoffIndices_card_le_enlarged_degree A.support R'.raw R'.enlarged_support D
      (fun i => (tensorSupportDegree_le_original A i).trans R'.degree) x
  exact hProvider (Fin A.count) (tensorChartFamilyOfAtlas A) hA.chart_mem R'.raw
    R'.smooth R'.inner_support hCount R'.own_jets R'.transition_jets p i j y hy

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNovParent_local_count
#print axioms GlobalEmbedding.Continuation.sourceCollarNov_parent_uniform_normalized_jets
