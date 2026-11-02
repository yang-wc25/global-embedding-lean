import FaithfulIncrements.ProtectedParentNeighborhoods
import FaithfulRepair.ProtectedBufferedGivenFiniteness

/-!
# One finite localization retains the whole parent and numerical buffers

The compact half-thickenings and all parent parameter projections enter
the choice of the local domains. The same physical parent cutoff therefore
remains admissible for the same counted grid after all-order given-input
finiteness is produced. No original norm domain or compact sample changes.
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

/-- The whole original parent and the common half-buffer survive one
localization, whose all-order given-input finiteness is proved internally. -/
theorem original_parent_buffer_preserving_given_finiteness
    (buffer : ℝ) (hbuffer : 0 < buffer)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k)
    (hGeometry : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hParent : ∀ i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1)
    (K : Fin Data.primaryCount → Fin Data.atlas.count × Fin Data.parameterCount → Set X)
    (hK : ∀ nu i, IsCompact (K nu i))
    (hBuffer : ∀ nu i x, x ∈ K nu i →
      ball x buffer ⊆ actualOriginalPrimaryNativeOpen Data nu i) :
    ∃ (V : Set P) (domain : Fin Data.primaryCount → Set (P × M)),
      IsOpen V ∧ Data.parameterSet ⊆ V ∧ closure V ⊆ Data.parameterOpen ∧
      IsCompact (closure V) ∧
      (∀ nu, IsOpen (domain nu)) ∧
      (∀ nu, IsCompact (closure (domain nu))) ∧
      (∀ nu, closure (domain nu) ⊆
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      (∀ nu, incrementsOriginalRelativeCutoffSupport
        (localPrimaryData Data V domain) nu ⊆ domain nu) ∧
      (∀ i, tsupport (theta i) ⊆
        (((localPrimaryData Data V domain).parameterChart i.2).source ∩
          (localPrimaryData Data V domain).parameterOpen) ×ˢ
          (localPrimaryData Data V domain).atlas.inner i.1) ∧
      (∀ nu i, cthickening (buffer/2) (K nu i) ⊆
        actualOriginalPrimaryNativeOpen (localPrimaryData Data V domain) nu i) ∧
      (∀ nu i x, x ∈ K nu i → ball x (buffer/2) ⊆
        actualOriginalPrimaryNativeOpen (localPrimaryData Data V domain) nu i) ∧
      ∀ j ell, actualOriginalGivenInputProfile (localPrimaryData Data V domain) j ell ≠ ⊤ := by
  let C := fun nu i => cthickening (buffer/2) (K nu i)
  have hC : ∀ nu i, IsCompact (C nu i) := fun nu i => (hK nu i).cthickening
  have hNative : ∀ nu i, C nu i ⊆ actualOriginalPrimaryNativeOpen Data nu i := by
    intro nu i z hz
    change z ∈ cthickening (buffer/2) (K nu i) at hz
    rw [(hK nu i).cthickening_eq_biUnion_closedBall (by positivity)] at hz
    obtain ⟨x, hx, hxz⟩ := mem_iUnion₂.mp hz
    exact hBuffer nu i x hx ((closedBall_subset_ball (half_lt_self hbuffer)) hxz)
  let parents : Set P := ⋃ i, Prod.fst '' tsupport (theta i)
  have hParents : IsCompact parents :=
    isCompact_iUnion (fun i => (hCompact i).image continuous_fst)
  have hParentsDomain : parents ⊆ Data.parameterOpen := by
    intro p hp
    obtain ⟨i,z,hz,rfl⟩ := mem_iUnion.mp hp
    exact (hParent i hz).1.2
  obtain ⟨V,domain,hV,hKV,hVU,hVC,hPV,hOpen,hClosedCompact,hClosure,hSupport,hCore⟩ :=
    original_parent_protected_primary_neighborhoods Data hd parents hParents hParentsDomain
      (originalProtectedNativePrimaryCore Data C)
      (originalProtectedNativePrimaryCore_isCompact Data C hC hNative)
      (originalProtectedNativePrimaryCore_subset Data C hNative)
  have hProtected : ∀ nu i, C nu i ⊆
      actualOriginalPrimaryNativeOpen (localPrimaryData Data V domain) nu i := by
    intro nu i z hz
    have hh := (round3Parameter_originalNativeOpen_iff Data i z).mp
      (round3_prepared_primary_native_subset Data i nu (hNative nu i hz))
    exact round3_prepared_native_primary_mem (localPrimaryData Data V domain) i nu z
      hh.1 hh.2.1 (hCore nu (mem_iUnion.mpr ⟨i,z,hz,rfl⟩))
  refine ⟨V,domain,hV,hKV,hVU,hVC,hOpen,hClosedCompact,hClosure,hSupport,?_,hProtected,?_,?_⟩
  · intro i z hz
    exact ⟨⟨(hParent i hz).1.1,hPV (mem_iUnion.mpr ⟨i,z,hz,rfl⟩)⟩,(hParent i hz).2⟩
  · intro nu i x hx
    exact (ball_subset_closedBall.trans (closedBall_subset_cthickening hx (buffer/2))).trans
      (hProtected nu i)
  · exact local_original_given_profile_finite Data hd hs hLinear V domain hOpen hClosedCompact
      hClosure Parameter Spatial hParameter hSpatial hGeometry

end GlobalEmbedding.Continuation.FaithfulRepair

#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_parent_buffer_preserving_given_finiteness
