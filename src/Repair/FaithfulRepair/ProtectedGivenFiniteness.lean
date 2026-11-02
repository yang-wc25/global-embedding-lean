import FaithfulRepair.OriginalGivenFiniteness
import FaithfulIncrements.ProtectedNativeCarriers

/-!
# All-order given-input finiteness with the quantitative native carriers kept

The original qualitative finiteness argument applies to the newly chosen
precompact neighborhoods. Their construction protects the same original
native compact sets and their parameter projections. Consequently all
orders are finite on one local datum while previously proved buffers in
the protected sets retain their exact numerical radius. This proves a
supplier property; it does not assume the given-input finiteness conclusion.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulRepair
open FaithfulIncrements FaithfulIntegration

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

/-- One actual local datum simultaneously retains the original native
compact carriers and has finite all-order given profiles. Neither the
original sample domains nor the given physical fields are changed. -/
theorem original_protected_given_finite_neighborhoods
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k)
    (hGeometry : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (C : Fin Data.primaryCount →
      Fin Data.atlas.count × Fin Data.parameterCount → Set X)
    (hC : ∀ nu i, IsCompact (C nu i))
    (hNative : ∀ nu i, C nu i ⊆ actualOriginalPrimaryNativeOpen Data nu i) :
    ∃ (V : Set P) (domain : Fin Data.primaryCount → Set (P × M)),
      IsOpen V ∧ Data.parameterSet ⊆ V ∧ closure V ⊆ Data.parameterOpen ∧
      IsCompact (closure V) ∧
      (∀ nu, IsOpen (domain nu)) ∧
      (∀ nu, IsCompact (closure (domain nu))) ∧
      (∀ nu, closure (domain nu) ⊆
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      (∀ nu, incrementsOriginalRelativeCutoffSupport
        (localPrimaryData Data V domain) nu ⊆ domain nu) ∧
      (∀ nu i, C nu i ⊆
        actualOriginalPrimaryNativeOpen (localPrimaryData Data V domain) nu i) ∧
      ∀ j ell, actualOriginalGivenInputProfile (localPrimaryData Data V domain) j ell ≠ ⊤ := by
  obtain ⟨V, domain, hV, hKV, hVU, hVC, hOpen, hCompact, hClosure, hSupport, hProtected⟩ :=
    original_protected_native_primary_neighborhoods Data hd C hC hNative
  refine ⟨V, domain, hV, hKV, hVU, hVC, hOpen, hCompact, hClosure, hSupport, hProtected, ?_⟩
  exact local_original_given_profile_finite Data hd hs hLinear V domain hOpen hCompact hClosure
    Parameter Spatial hParameter hSpatial hGeometry

end GlobalEmbedding.Continuation.FaithfulRepair

#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_protected_given_finite_neighborhoods
