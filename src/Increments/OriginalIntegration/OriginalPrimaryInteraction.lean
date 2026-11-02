import IncrementsCompletion.OriginalRelativeSupportMultiplicity
import FaithfulIntegration.LocalizedDataTransport
import FaithfulCollars.GlobalFromLocalRaw

/-!
# The actual original interaction degree, not the total label count

The finite decomposition is fixed in `lem:increments`. Its original relative
cutoff supports, restricted to the prescribed compact parameter samples,
determine a genuine intersection graph. Its maximum degree gives a proved
local multiplicity. No count of the whole primary family is used by this
bound, and no multiplicity certificate is requested from the caller.

For a class of decompositions a common degree or per-host piece budget must
still come from `setup:uniform`; merely defining this fixed-data degree does
not move the atlas or decomposition behind a uniform numerical constant.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation.OriginalIntegration
open FaithfulIncrements FaithfulIntegration FaithfulCollars

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]

def originalPrimarySampleSupport (Data : IncrementsOriginalNativeData n d N M P)
    (nu : Fin Data.primaryCount) : Set (P × M) :=
  (Data.parameterSet ×ˢ (univ : Set M)) ∩ incrementsOriginalRelativeCutoffSupport Data nu

def originalPrimaryInteractionDegree (Data : IncrementsOriginalNativeData n d N M P) : ℕ :=
  Finset.univ.sup (tensorEnlargedSupportDegree (originalPrimarySampleSupport Data))

theorem originalPrimaryInteractionDegree_bound
    (Data : IncrementsOriginalNativeData n d N M P) (nu : Fin Data.primaryCount) :
    tensorEnlargedSupportDegree (originalPrimarySampleSupport Data) nu ≤
      originalPrimaryInteractionDegree Data :=
  Finset.le_sup (Finset.mem_univ nu)

/-- The exact sample-wise relative supports supply their own local count. -/
theorem original_primary_interaction_count
    (Data : IncrementsOriginalNativeData n d N M P)
    (z : P × M) (hz : z ∈ Data.parameterSet ×ˢ (univ : Set M)) :
    (Finset.univ.filter (fun nu => z ∈ incrementsOriginalRelativeCutoffSupport Data nu)).card ≤
      originalPrimaryInteractionDegree Data + 1 := by
  have h := incrementsCompletion_original_hosts_through_point
    (originalPrimarySampleSupport Data) (originalPrimaryInteractionDegree Data)
    (originalPrimaryInteractionDegree_bound Data) z
  simpa only [originalPrimarySampleSupport, mem_inter_iff, hz, true_and] using h

/-- A genuine original support budget controls the manufactured degree.
It is a bound on given geometric sets, not on a future solver output. -/
theorem originalPrimaryInteractionDegree_le
    (Data : IncrementsOriginalNativeData n d N M P) (W : Fin Data.primaryCount → Set (P × M))
    (D : ℕ) (hW : ∀ nu, originalPrimarySampleSupport Data nu ⊆ W nu)
    (hD : ∀ nu, tensorEnlargedSupportDegree W nu ≤ D) :
    originalPrimaryInteractionDegree Data ≤ D := by
  apply Finset.sup_le
  intro nu _
  exact (enlargedSupportDegree_mono _ W hW nu).trans (hD nu)

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- Internal parameter/solver localization only decreases that exact count. -/
theorem original_primary_localized_interaction_count
    (Data : IncrementsOriginalNativeData n d N M P)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hV : V ⊆ Data.parameterOpen)
    (z : P × M) (hz : z ∈ Data.parameterSet ×ˢ (univ : Set M)) :
    (Finset.univ.filter (fun nu => z ∈
      incrementsOriginalRelativeCutoffSupport (localPrimaryData Data V domain) nu)).card ≤
      originalPrimaryInteractionDegree Data + 1 := by
  apply (Finset.card_le_card ?_).trans (original_primary_interaction_count Data z hz)
  intro nu hnu
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  exact localPrimaryData_relative_support_subset Data V domain hV nu
    (Finset.mem_filter.mp hnu).2

end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.original_primary_interaction_count
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.original_primary_localized_interaction_count
