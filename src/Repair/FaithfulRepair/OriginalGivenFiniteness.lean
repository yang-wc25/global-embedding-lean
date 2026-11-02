import FaithfulRepair.OriginalCoreFiniteness
import FaithfulIntegration.OriginalLinearFiniteness

/-!
# Full actual given-input profile from original smooth inputs

Every component is produced from the same original fields and original
transition geometry: F, H, cutoff, provided normal, spatial and total phase
covectors, symmetric linear argument and original transition differential.
The same internal primary neighborhoods are chosen before every order.
No component's high-order norm finiteness is an entrance hypothesis.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulRepair
open FaithfulIncrements FaithfulIntegration

private theorem given_finite_max {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : max a b ≠ ⊤ :=
  ne_of_lt (max_lt (lt_top_iff_ne_top.mpr ha) (lt_top_iff_ne_top.mpr hb))

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- Literal full actual given profile, assembled exclusively from its
proved original-field producers.  Its low-order numerical budget is not
changed; these are qualitative high-order finiteness proofs. -/
theorem local_original_given_profile_finite
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hOpen : ∀ nu, IsOpen (domain nu))
    (hCompact : ∀ nu, IsCompact (closure (domain nu)))
    (hClosure : ∀ nu, closure (domain nu) ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k)
    (hGeometry : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (j : ℕ) (ell : ℝ) :
    actualOriginalGivenInputProfile (localPrimaryData Data V domain) j ell ≠ ⊤ := by
  let T := originalJointTransitionProfile (m+1) d Parameter Spatial
  have hT : ∀ k, 0 ≤ T k := originalJointTransitionProfile_nonneg _ _ _ _ hParameter
  have hJoint := repairOriginalTransitionBudgets_joint Data hd Parameter Spatial hGeometry
  have hSource := repairOriginalTransitionBudgets_source Data hd Parameter Spatial hGeometry
  unfold actualOriginalGivenInputProfile incrementsOriginalInputProfileWithLinear
  apply given_finite_max
  · apply given_finite_max
    · exact local_original_core_profile_finite Data hd hs V domain hOpen hCompact hClosure
        Parameter Spatial hParameter hSpatial hGeometry j ell
    · apply iSup_ne_top
      intro nu
      exact local_primary_linear_weighted_finite Data hd hLinear V domain nu
        (hOpen nu) (hCompact nu) (hClosure nu) T Spatial hT hSpatial hJoint hSource 0 j ell
  · apply given_finite_max
    · apply iSup_ne_top
      intro nu
      exact local_primary_total_phase_weighted_finite Data hd hs V domain nu
        (hOpen nu) (hCompact nu) (hClosure nu) T hT hJoint 0 j ell
    · exact original_transition_differential_finite_of_original_geometry Data hd Parameter Spatial
        hGeometry 0 j ell

/-- A complete qualitative supplier: the actual solver neighborhoods and
the entire all-order given profile are constructed from the original
smooth data and original transition budgets.  The same neighborhoods serve
every j and ell.  Original F/H, Omega/Q/K and all physical fields are kept. -/
theorem original_local_given_finite_neighborhoods
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k)
    (hGeometry : RepairOriginalTransitionBudgets Data Parameter Spatial) :
    ∃ (V : Set P) (domain : Fin Data.primaryCount → Set (P × M)),
      IsOpen V ∧ Data.parameterSet ⊆ V ∧ closure V ⊆ Data.parameterOpen ∧
      IsCompact (closure V) ∧
      (∀ nu, IsOpen (domain nu)) ∧
      (∀ nu, IsCompact (closure (domain nu))) ∧
      (∀ nu, closure (domain nu) ⊆ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      (∀ nu, incrementsOriginalRelativeCutoffSupport (localPrimaryData Data V domain) nu ⊆ domain nu) ∧
      ∀ j ell, actualOriginalGivenInputProfile (localPrimaryData Data V domain) j ell ≠ ⊤ := by
  obtain ⟨V,domain,hV,hKV,hVU,hVC,hOpen,hCompact,hClosure,hSupport⟩ :=
    original_local_primary_neighborhoods Data hd
  refine ⟨V,domain,hV,hKV,hVU,hVC,hOpen,hCompact,hClosure,hSupport,?_⟩
  exact local_original_given_profile_finite Data hd hs hLinear V domain hOpen hCompact hClosure
    Parameter Spatial hParameter hSpatial hGeometry

end GlobalEmbedding.Continuation.FaithfulRepair

#print axioms GlobalEmbedding.Continuation.FaithfulRepair.local_original_given_profile_finite
#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_local_given_finite_neighborhoods
