import NormalPolar.JointSecondarySignedNativeProfiles

/-! The canonical native parameter chart preserves the actual closed spatial
cutoff carrier. The proof takes relative topological support on the whole
original native domain; it makes no openness assumption on that carrier. -/

noncomputable section
open Set Function GlobalEmbedding.Paper
open scoped Topology
namespace GlobalEmbedding.Continuation

theorem jointSecondary_native_spatial_cutoff_carrier
    {M P Ep : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    (B : OpenPartialHomeomorph P Ep) (chi : M → ℝ) :
    incrementsGlobalRelativeSupport (round3ParameterNativeDomain B (univ : Set (P × M)))
      (fun z : Ep × M => chi z.2) ⊆
      round3ParameterNativeDomain B ((univ : Set P) ×ˢ tsupport chi) := by
  rintro _ ⟨z,hz,rfl⟩
  exact ⟨z.property.1,mem_univ _,
    tsupport_comp_subset_preimage chi continuous_subtype_val.snd hz⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_native_spatial_cutoff_carrier
