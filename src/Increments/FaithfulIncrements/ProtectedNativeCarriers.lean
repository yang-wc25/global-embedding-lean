import FaithfulIncrements.ProtectedPrimaryNeighborhoods
import Probes.Round3PreparedOriginalDomains
import Probes.Round3ParameterCrossNativeData

/-!
# Preserve actual native compact carriers through primary localization

Each protected set lives in the literal original observing coordinates.
Its inverse image under that original product chart is compact. The finite
union over observing charts is inserted before choosing the local primary
and parameter domains. This retains the same native sets, hence every
previously proved numerical ball inclusion in them, without changing any
original sample domain or norm.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulIncrements

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

/-- The same original physical carrier, obtained from the original native
compact sets. There is no choice of an adapted chart in this definition. -/
def originalProtectedNativePrimaryCore
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (C : Fin Data.primaryCount →
      Fin Data.atlas.count × Fin Data.parameterCount → Set X)
    (nu : Fin Data.primaryCount) : Set (P × M) :=
  ⋃ i, ((Data.parameterChart i.2).prod (Data.atlas.chart i.1)).symm '' C nu i

theorem originalProtectedNativePrimaryCore_isCompact
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (C : Fin Data.primaryCount →
      Fin Data.atlas.count × Fin Data.parameterCount → Set X)
    (hC : ∀ nu i, IsCompact (C nu i))
    (hNative : ∀ nu i, C nu i ⊆ actualOriginalPrimaryNativeOpen Data nu i)
    (nu : Fin Data.primaryCount) :
    IsCompact (originalProtectedNativePrimaryCore Data C nu) := by
  apply isCompact_iUnion
  intro i
  apply (hC nu i).image_of_continuousOn
  apply ((Data.parameterChart i.2).prod (Data.atlas.chart i.1)).symm.continuousOn.mono
  intro z hz
  have hh := (round3Parameter_originalNativeOpen_iff Data i z).mp
    (round3_prepared_primary_native_subset Data i nu (hNative nu i hz))
  exact ⟨hh.2.1, hh.1⟩

theorem originalProtectedNativePrimaryCore_subset
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (C : Fin Data.primaryCount →
      Fin Data.atlas.count × Fin Data.parameterCount → Set X)
    (hNative : ∀ nu i, C nu i ⊆ actualOriginalPrimaryNativeOpen Data nu i)
    (nu : Fin Data.primaryCount) :
    originalProtectedNativePrimaryCore Data C nu ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data := by
  intro z hz
  obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hz
  exact round3_prepared_native_primary_active Data i nu (hNative nu i hx)

/-- Construct one localization preserving every original native compact
carrier. In particular the parameter neighborhood is chosen around their
projections, not only around the compact parameter evaluation set. -/
theorem original_protected_native_primary_neighborhoods
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
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
        actualOriginalPrimaryNativeOpen (localPrimaryData Data V domain) nu i) := by
  obtain ⟨V, domain, hV, hKV, hVU, hVC, hOpen, hCompact, hClosure, hSupport, hProtected⟩ :=
    original_protected_primary_neighborhoods Data hd (originalProtectedNativePrimaryCore Data C)
      (originalProtectedNativePrimaryCore_isCompact Data C hC hNative)
      (originalProtectedNativePrimaryCore_subset Data C hNative)
  refine ⟨V, domain, hV, hKV, hVU, hVC, hOpen, hCompact, hClosure, hSupport, ?_⟩
  intro nu i z hz
  have hCore : ((Data.parameterChart i.2).prod (Data.atlas.chart i.1)).symm z ∈
      originalProtectedNativePrimaryCore Data C nu :=
    mem_iUnion.mpr ⟨i, z, hz, rfl⟩
  have hh := (round3Parameter_originalNativeOpen_iff Data i z).mp
    (round3_prepared_primary_native_subset Data i nu (hNative nu i hz))
  exact round3_prepared_native_primary_mem (localPrimaryData Data V domain) i nu z
    hh.1 hh.2.1 (hProtected nu hCore)

/-- A numerical ball already contained in a retained native carrier stays
inside the actual local primary domain, with its radius unchanged. -/
theorem protected_native_ball_preserved
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (C : Fin Data.primaryCount →
      Fin Data.atlas.count × Fin Data.parameterCount → Set X)
    (hProtected : ∀ nu i, C nu i ⊆
      actualOriginalPrimaryNativeOpen (localPrimaryData Data V domain) nu i)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (x : X) (radius : ℝ) (hBall : ball x radius ⊆ C nu i) :
    ball x radius ⊆ actualOriginalPrimaryNativeOpen (localPrimaryData Data V domain) nu i :=
  hBall.trans (hProtected nu i)

end GlobalEmbedding.Continuation.FaithfulIncrements

#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.original_protected_native_primary_neighborhoods
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.protected_native_ball_preserved
