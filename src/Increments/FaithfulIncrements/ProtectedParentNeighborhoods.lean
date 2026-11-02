import FaithfulIncrements.ProtectedNativeCarriers

/-!
# Protect parent parameters as well as active primary carriers

The primary carriers alone do not contain the inactive part of a parent
cutoff. To keep the very same parent after parameter localization, its
compact parameter projection must be included before choosing the outer
neighborhood. The original compact evaluation set remains unchanged.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulIncrements

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- The local primary and parameter domains contain both the compact
active carriers and an arbitrary compact set of original parameters. -/
theorem original_parent_protected_primary_neighborhoods
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (parents : Set P) (hParents : IsCompact parents)
    (hParentsDomain : parents ⊆ Data.parameterOpen)
    (core : Fin Data.primaryCount → Set (P × M))
    (hCore : ∀ nu, IsCompact (core nu))
    (hCoreDomain : ∀ nu, core nu ⊆
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :
    ∃ (V : Set P) (domain : Fin Data.primaryCount → Set (P × M)),
      IsOpen V ∧ Data.parameterSet ⊆ V ∧ closure V ⊆ Data.parameterOpen ∧
      IsCompact (closure V) ∧ parents ⊆ V ∧
      (∀ nu, IsOpen (domain nu)) ∧
      (∀ nu, IsCompact (closure (domain nu))) ∧
      (∀ nu, closure (domain nu) ⊆
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      (∀ nu, incrementsOriginalRelativeCutoffSupport
        (localPrimaryData Data V domain) nu ⊆ domain nu) ∧
      (∀ nu, core nu ⊆ domain nu ∩
        incrementsOriginalParameterRegion (localPrimaryData Data V domain)) := by
  letI : LocallyCompactSpace P :=
    ChartedSpace.locallyCompactSpace (H := EuclideanSpace ℝ (Fin d)) (M := P)
  let parameters : Set P := (Data.parameterSet ∪ parents) ∪ ⋃ nu, Prod.fst '' core nu
  have hParameters : IsCompact parameters :=
    (hd.parameter_compact.union hParents).union
      (isCompact_iUnion (fun nu => (hCore nu).image continuous_fst))
  have hParametersDomain : parameters ⊆ Data.parameterOpen := by
    intro p hp
    rcases hp with hp | hp
    · exact hp.elim (fun hp => hd.parameter_subset hp) (fun hp => hParentsDomain hp)
    · obtain ⟨nu, z, hz, rfl⟩ := mem_iUnion.mp hp
      exact (hCoreDomain nu hz).2.1
  obtain ⟨V, hV, hParametersV, hVU, hVC⟩ :=
    exists_open_between_and_isCompact_closure hParameters hd.parameter_open hParametersDomain
  have hKV : Data.parameterSet ⊆ V := fun p hp => hParametersV (Or.inl (Or.inl hp))
  have hPV : parents ⊆ V := fun p hp => hParametersV (Or.inl (Or.inr hp))
  have hCoreV (nu : Fin Data.primaryCount) (z : P × M) (hz : z ∈ core nu) :
      z.1 ∈ V := hParametersV (Or.inr (mem_iUnion.mpr ⟨nu, z, hz, rfl⟩))
  have hEach (nu : Fin Data.primaryCount) : ∃ U : Set (P × M),
      IsOpen U ∧
      (((closure V ×ˢ (univ : Set M)) ∩
        incrementsOriginalRelativeCutoffSupport Data nu) ∪ core nu) ⊆ U ∧
      closure U ⊆ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data ∧
      IsCompact (closure U) := by
    apply exists_open_between_and_isCompact_closure
      ((original_active_primary_carrier_compact Data (closure V) hVC hVU nu).union (hCore nu))
      ((hd.primary_open nu).inter (hd.parameter_open.prod isOpen_univ))
    intro z hz
    rcases hz with hz | hz
    · exact ⟨hd.cutoff_support_local nu hz.2,
        incrementsOriginalRelativeCutoffSupport_subset Data nu hz.2⟩
    · exact hCoreDomain nu hz
  choose domain hOpen hCover hClosure hCompact using hEach
  refine ⟨V, domain, hV, hKV, hVU, hVC, hPV, hOpen, hCompact, hClosure, ?_, ?_⟩
  · intro nu z hz
    have hzOld := localPrimaryData_relative_support_subset Data V domain
      (subset_closure.trans hVU) nu hz
    have hzV := incrementsOriginalRelativeCutoffSupport_subset
      (localPrimaryData Data V domain) nu hz
    exact hCover nu (Or.inl ⟨⟨subset_closure hzV.1, hzV.2⟩, hzOld⟩)
  · intro nu z hz
    exact ⟨hCover nu (Or.inr hz), hCoreV nu z hz, mem_univ _⟩

end GlobalEmbedding.Continuation.FaithfulIncrements

#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.original_parent_protected_primary_neighborhoods
