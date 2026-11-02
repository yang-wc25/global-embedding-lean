import RepairClosure.EndpointSmallImmersionStatements
import RepairClosure.GeometrySmallImmersionApplication

/-!
# Small exact immersion against the independent complete source target

The actual initialization, repair and rescaling application supplies one
map. This proof exposes every field for that same map in the independently
spelled target. No general native uniform-repair theorem is a premise.
-/

noncomputable section
namespace GlobalEmbedding.Continuation.RepairClosure
universe uM

theorem original_small_exact_immersion_candidate :
    EndpointSmallExactImmersionTarget.{uM} := by
  intro n M _ _ _ _ _ _ hn hpar metric0 r hr
  obtain ⟨F,hF⟩ := small_exact_immersion hn hpar metric0 r hr
  exact ⟨F,hF.smooth,hF.exact_metric,hF.immersion,hF.phase_regular,hF.image_bound⟩

end GlobalEmbedding.Continuation.RepairClosure

#print axioms GlobalEmbedding.Continuation.RepairClosure.original_small_exact_immersion_candidate
