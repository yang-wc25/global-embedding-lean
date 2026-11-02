import FaithfulRepair.OriginalTransitionDifferentialFiniteness
import FaithfulIncrements.LocalPhaseFiniteness

/-! The complete original Core profile is finite from the original smooth
fields and geometry.  The internal primary neighborhoods are manufactured
around the original supports.  All physical fields, original Omega/Q/K,
and the map/tensor observation domains remain the original ones. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulRepair
open FaithfulIncrements

private theorem finite_max {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : max a b ≠ ⊤ :=
  ne_of_lt (max_lt (lt_top_iff_ne_top.mpr ha) (lt_top_iff_ne_top.mpr hb))

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- No component's norm finiteness is an input: F, H, cutoff, provided
normal and the actual spatial phase covector are all produced internally. -/
theorem local_original_core_profile_finite
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hOpen : ∀ nu, IsOpen (domain nu))
    (hCompact : ∀ nu, IsCompact (closure (domain nu)))
    (hClosure : ∀ nu, closure (domain nu) ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k)
    (hGeometry : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (j : ℕ) (ell : ℝ) :
    incrementsOriginalCoreInputProfile (localPrimaryData Data V domain) j ell ≠ ⊤ := by
  let T := originalJointTransitionProfile (m+1) d Parameter Spatial
  have hT : ∀ k, 0 ≤ T k := originalJointTransitionProfile_nonneg _ _ _ _ hParameter
  have hTransition := repairOriginalTransitionBudgets_joint Data hd Parameter Spatial hGeometry
  unfold incrementsOriginalCoreInputProfile
  apply finite_max
  · exact original_map_weighted_finite_of_original_geometry Data hd hs Parameter Spatial hParameter
      hGeometry 2 j ell
  · apply finite_max
    · exact original_tensor_weighted_finite_of_original_geometry Data hd hs Parameter Spatial
        hParameter hSpatial hGeometry 0 j ell
    · apply iSup_ne_top
      intro nu
      apply finite_max
      · exact local_primary_cutoff_weighted_finite Data hd hs V domain nu
          (hOpen nu) (hCompact nu) (hClosure nu) T hT hTransition 0 j ell
      · apply finite_max
        · exact local_primary_normal_weighted_finite Data hd hs V domain nu
            (hOpen nu) (hCompact nu) (hClosure nu) T hT hTransition 0 j ell
        · exact local_primary_spatial_phase_weighted_finite Data hd hs V domain nu
            (hOpen nu) (hCompact nu) (hClosure nu) T hT hTransition 0 j ell

end GlobalEmbedding.Continuation.FaithfulRepair

#print axioms GlobalEmbedding.Continuation.FaithfulRepair.local_original_core_profile_finite
