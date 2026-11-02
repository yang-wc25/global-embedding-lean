import Probes.ActualIncrementRawObserverDomains
import Probes.ActualFinalHostRawProfiles

/-! Exact host-domain and sample identities for the actual final G. These
eliminate an artificial observer-domain hypothesis once the original producer
exposes its canonical observer open set. -/
noncomputable section
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Classical
namespace GlobalEmbedding.Continuation
variable {m : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem actual_secondary_host_source_subset_canonical_observer
    (e : OpenPartialHomeomorph M D) (a : OpenPartialHomeomorph (Ep × M) X)
    (G : Set (Ep × M)) (hsource : a.source ⊆ G) :
    (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans a).source ⊆ actualRawObserverOpen e G := by
  intro z hz
  exact ⟨hz.1,hsource hz.2⟩

theorem actual_secondary_host_inverse_sample_identity
    (b a : OpenPartialHomeomorph (Ep × M) X) (S : Set (Ep × M)) (hS : S ⊆ a.source) :
    (b.symm.trans a).symm '' (a '' S) = b '' S := by
  ext z
  constructor
  · rintro ⟨w,⟨y,hy,rfl⟩,rfl⟩
    change b (a.symm (a y)) ∈ b '' S
    rw [a.left_inv (hS hy)]
    exact ⟨y,hy,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    refine ⟨a y,⟨y,hy,rfl⟩,?_⟩
    change b (a.symm (a y)) = b y
    rw [a.left_inv (hS hy)]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_secondary_host_source_subset_canonical_observer
#print axioms GlobalEmbedding.Continuation.actual_secondary_host_inverse_sample_identity
