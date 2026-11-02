import RepairClosure.EndpointIncrementStatements
import RepairClosure.EndpointIncrementFiniteVector
import OriginalIntegration.SampledFixedDataFinitePrefixTarget
import OriginalIntegration.BoundedSampledRegionPrimitivePhaseIncrement
import OriginalIncrements.CommonFiniteThresholdPhi

/-!
# Original increment candidate proofs against independent statement definitions

The independent Challenge imports only the two statement files.  This
solution imports the real producers and proves the same named targets.
There are no placeholders and no proof-level imports from that Challenge.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GlobalEmbedding.Continuation.RepairClosure
universe uM uP

theorem original_increment_fixed_data_candidate :
    EndpointFixedIncrementTarget.{uM,uP} := by
  exact @GlobalEmbedding.Paper.finite_positive_increments_fixed_data

theorem original_increment_finite_entrance_candidate :
    EndpointSampledIncrementTarget.{uM,uP} := by
  exact @GlobalEmbedding.Paper.finite_positive_increments_sampled_fixed_data_finite_prefix

theorem original_increment_bounded_class_candidate :
    EndpointBoundedIncrementTarget.{uM,uP} := by
  exact @OriginalIntegration.bounded_sampled_region_primitive_phase_increment

theorem original_increment_finite_vector_candidate :
    EndpointIncrementFiniteVectorTarget.{uM} := by
  exact @OriginalIncrements.commonFiniteThreshold_eq_phi

end GlobalEmbedding.Continuation.RepairClosure

#print axioms GlobalEmbedding.Continuation.RepairClosure.original_increment_fixed_data_candidate
#print axioms GlobalEmbedding.Continuation.RepairClosure.original_increment_finite_entrance_candidate
#print axioms GlobalEmbedding.Continuation.RepairClosure.original_increment_bounded_class_candidate
#print axioms GlobalEmbedding.Continuation.RepairClosure.original_increment_finite_vector_candidate
