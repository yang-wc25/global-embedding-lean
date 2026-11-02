import Probes.ActualRelativeInteractionCarrier
import Smoothing.Round3RepairNormalRebind
import Mathlib.Topology.Separation.Regular

/-!
# Construct internal primary neighborhoods around the actual original supports

The original given functions and all original norm/differentiation/sample
domains are retained.  Only a local solver's primary-domain annotation and its
parameter-open neighborhood are restricted.  The restriction is manufactured
from the original compact parameter set and the actual relative cutoff
supports. It is chosen once, before any observation order.

This implements the subordinate-local-chart step in the proof of
lem:increments. It removes an unnecessary demand for high-order control of
phase/normal/linear data arbitrarily close to the boundary of an unused
primary domain. It does not assert a numerical bound for the new neighborhood
or solve the remaining quantitative uniformity of the adapted-chart supplier.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulIncrements

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- Internal domain annotations only. No original field function, norm domain,
chart, compact parameter sample, or original decomposition is replaced. -/
def localPrimaryData
    (Data : IncrementsOriginalNativeData n d N M P)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M)) :
    IncrementsOriginalNativeData n d N M P :=
  { Data with parameterOpen := V, primaryDomain := domain }

theorem localPrimaryData_relative_support_subset
    (Data : IncrementsOriginalNativeData n d N M P)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hV : V ⊆ Data.parameterOpen) (nu : Fin Data.primaryCount) :
    incrementsOriginalRelativeCutoffSupport (localPrimaryData Data V domain) nu ⊆
      incrementsOriginalRelativeCutoffSupport Data nu := by
  exact actual_relative_support_pullback_subset (V ×ˢ (univ : Set M))
    (incrementsOriginalParameterRegion Data) id continuous_id.continuousOn
    (fun z hz => ⟨hV hz.1, hz.2⟩) (Data.cutoff nu)

/-- The whole active original support over a compact parameter neighborhood
is compact even though the original relative support need not be globally
closed and the original coordinate norm domains need not be compact. -/
theorem original_active_primary_carrier_compact [CompactSpace M]
    (Data : IncrementsOriginalNativeData n d N M P)
    (K : Set P) (hK : IsCompact K) (hKU : K ⊆ Data.parameterOpen)
    (nu : Fin Data.primaryCount) :
    IsCompact ((K ×ˢ (univ : Set M)) ∩ incrementsOriginalRelativeCutoffSupport Data nu) := by
  have h := actual_compact_interaction_carrier (K ×ˢ (univ : Set M))
    (incrementsOriginalParameterRegion Data) (hK.prod isCompact_univ)
    (fun z hz => ⟨hKU hz.1, hz.2⟩) (Data.cutoff nu) (Data.cutoff nu)
  simpa only [inter_self, incrementsOriginalRelativeCutoffSupport] using h

/-- One genuine finite family of local solver neighborhoods is manufactured
from the unchanged original data. The same neighborhoods serve every order.
Hausdorffness is the usual manifold separation property, not a norm estimate. -/
theorem original_local_primary_neighborhoods [T2Space M] [T2Space P] [CompactSpace M]
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) :
    ∃ (V : Set P) (domain : Fin Data.primaryCount → Set (P × M)),
      IsOpen V ∧ Data.parameterSet ⊆ V ∧ closure V ⊆ Data.parameterOpen ∧
      IsCompact (closure V) ∧
      (∀ nu, IsOpen (domain nu)) ∧
      (∀ nu, IsCompact (closure (domain nu))) ∧
      (∀ nu, closure (domain nu) ⊆ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      (∀ nu, incrementsOriginalRelativeCutoffSupport (localPrimaryData Data V domain) nu ⊆ domain nu) := by
  letI : LocallyCompactSpace P := ChartedSpace.locallyCompactSpace (H := Ep) (M := P)
  obtain ⟨V, hV, hKV, hVU, hVC⟩ :=
    exists_open_between_and_isCompact_closure hd.parameter_compact hd.parameter_open hd.parameter_subset
  have hEach (nu : Fin Data.primaryCount) : ∃ U : Set (P × M), IsOpen U ∧
      ((closure V ×ˢ (univ : Set M)) ∩ incrementsOriginalRelativeCutoffSupport Data nu) ⊆ U ∧
      closure U ⊆ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data ∧
      IsCompact (closure U) := by
    apply exists_open_between_and_isCompact_closure
      (original_active_primary_carrier_compact Data (closure V) hVC hVU nu)
      ((hd.primary_open nu).inter (hd.parameter_open.prod isOpen_univ))
    intro z hz
    exact ⟨hd.cutoff_support_local nu hz.2,
      incrementsOriginalRelativeCutoffSupport_subset Data nu hz.2⟩
  choose domain hOpen hCover hClosure hCompact using hEach
  refine ⟨V, domain, hV, hKV, hVU, hVC, hOpen, hCompact, hClosure, ?_⟩
  intro nu z hz
  have hzOld := localPrimaryData_relative_support_subset Data V domain
    (subset_closure.trans hVU) nu hz
  have hzV := incrementsOriginalRelativeCutoffSupport_subset (localPrimaryData Data V domain) nu hz
  exact hCover nu ⟨⟨subset_closure hzV.1, hzV.2⟩, hzOld⟩

/-- All original domain conditions follow for the actual internal restriction.
The source and parameter norm domains, compact parameter set, and charts are
definitionally the original ones. -/
def localPrimaryData_domain_conditions
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hV : IsOpen V) (hKV : Data.parameterSet ⊆ V)
    (hOpen : ∀ nu, IsOpen (domain nu))
    (hSupport : ∀ nu,
      incrementsOriginalRelativeCutoffSupport (localPrimaryData Data V domain) nu ⊆ domain nu) :
    IncrementsOriginalDomainConditions (localPrimaryData Data V domain) where
  source_dim := hd.source_dim
  target_dim := hd.target_dim
  parameter_open := hV
  parameter_compact := hd.parameter_compact
  parameter_subset := hKV
  atlas_smooth := hd.atlas_smooth
  parameter_charts_smooth := hd.parameter_charts_smooth
  source_norm_subset := hd.source_norm_subset
  source_inner_norm := hd.source_inner_norm
  parameter_norm_subset := hd.parameter_norm_subset
  parameter_cover := hd.parameter_cover
  primary_open := hOpen
  cutoff_support_local := hSupport

/-- Smoothness belongs to the same original functions and follows by locality. -/
def localPrimaryData_smooth_inputs
    (Data : IncrementsOriginalNativeData n d N M P)
    (hs : IncrementsOriginalSmoothInputs Data)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hV : V ⊆ Data.parameterOpen) (hDomain : ∀ nu, domain nu ⊆ Data.primaryDomain nu) :
    IncrementsOriginalSmoothInputs (localPrimaryData Data V domain) where
  F_joint := hs.F_joint.mono (fun z hz => ⟨hV hz.1, hz.2⟩)
  H_coordinates := fun i => (hs.H_coordinates i).mono
    (fun y hy => ⟨hy.1, hV hy.2.1, hy.2.2⟩)
  phase_joint := fun nu => (hs.phase_joint nu).mono
    (fun z hz => ⟨hDomain nu hz.1, hV hz.2.1, hz.2.2⟩)
  cutoff_joint := fun nu => (hs.cutoff_joint nu).mono
    (fun z hz => ⟨hDomain nu hz.1, hV hz.2.1, hz.2.2⟩)
  normal_joint := fun nu => (hs.normal_joint nu).mono
    (fun z hz => ⟨hDomain nu hz.1, hV hz.2.1, hz.2.2⟩)

/-- Original low-order bounds do not increase when an internal phase domain
is restricted. No original output evaluation set is restricted here. -/
theorem localPrimaryData_primary_weighted_le
    (Data : IncrementsOriginalNativeData n d N M P)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hOld : ∀ nu, IsOpen (Data.primaryDomain nu)) (hNew : ∀ nu, IsOpen (domain nu))
    (hSub : ∀ nu, domain nu ⊆ Data.primaryDomain nu)
    (nu : Fin Data.primaryCount) {a : ℕ}
    (f : (Fin Data.atlas.count × Fin Data.parameterCount) → (Fin (n+d) → ℝ) → Fin a → ℝ)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell f
      (incrementsOriginalPrimaryDifferentiation (localPrimaryData Data V domain) nu)
      (incrementsOriginalPrimaryEvaluation (localPrimaryData Data V domain) nu) ≤
    paperAtlasWeighted base j ell f
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) :=
  round3_repair_rebind_primary_weighted_le Data Data.freeNormal domain hOld hNew hSub nu f base j ell

end GlobalEmbedding.Continuation.FaithfulIncrements

#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.original_local_primary_neighborhoods
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.localPrimaryData_smooth_inputs
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.localPrimaryData_primary_weighted_le
