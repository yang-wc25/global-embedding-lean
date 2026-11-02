import OriginalCollars.FactoryCommonGeometryPacket
import FaithfulRepair.ProtectedParentGivenFiniteness

/-!
# Common geometry, the whole parent, and all-order finiteness in one datum

The same original scalar functions and original sample domains survive
the localization. The compact parent projections and the closed primary
half-buffers are protected before choosing the new domains. The actual
grid can then be run on that very finite datum at the fixed half-buffer.
No arbitrary smaller buffer or replacement parent enters this interface.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements
open FaithfulIncrements FaithfulRepair OriginalCollars

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
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)

/-- An actual internal localization of the original datum. The numerical
geometry, original kernel reserve, parent, and finite profiles all belong
to the identical local datum displayed in the fields. -/
structure OriginalProtectedCommonPrimaryData
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (mu Mb R buffer kappa : ℝ) where
  parameterOpen : Set P
  primaryDomain : Fin Data.primaryCount → Set (P × M)
  parameter_open : IsOpen parameterOpen
  parameter_sample : Data.parameterSet ⊆ parameterOpen
  parameter_closure : closure parameterOpen ⊆ Data.parameterOpen
  parameter_compact : IsCompact (closure parameterOpen)
  primary_open : ∀ nu, IsOpen (primaryDomain nu)
  primary_compact : ∀ nu, IsCompact (closure (primaryDomain nu))
  primary_closure : ∀ nu, closure (primaryDomain nu) ⊆
    Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data
  primary_support : ∀ nu, incrementsOriginalRelativeCutoffSupport
    (localPrimaryData Data parameterOpen primaryDomain) nu ⊆ primaryDomain nu
  parent_support : ∀ i, tsupport (theta i) ⊆
    (((localPrimaryData Data parameterOpen primaryDomain).parameterChart i.2).source ∩
      (localPrimaryData Data parameterOpen primaryDomain).parameterOpen) ×ˢ
      (localPrimaryData Data parameterOpen primaryDomain).atlas.inner i.1
  geometry : OriginalCommonPrimaryGeometry (localPrimaryData Data parameterOpen primaryDomain)
    theta mu Mb R (buffer/2)
  kernel : RepairOriginalPrimaryKernelInputs (localPrimaryData Data parameterOpen primaryDomain)
    (actualOriginalNativeOpen (localPrimaryData Data parameterOpen primaryDomain)) kappa
  given_finite : ∀ j ell,
    actualOriginalGivenInputProfile (localPrimaryData Data parameterOpen primaryDomain) j ell ≠ ⊤

def OriginalProtectedCommonPrimaryData.domain_conditions
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ}
    {mu Mb R buffer kappa : ℝ}
    (q : OriginalProtectedCommonPrimaryData Data theta mu Mb R buffer kappa)
    (hd : IncrementsOriginalDomainConditions Data) :
    IncrementsOriginalDomainConditions (localPrimaryData Data q.parameterOpen q.primaryDomain) :=
  localPrimaryData_domain_conditions Data hd q.parameterOpen q.primaryDomain q.parameter_open
    q.parameter_sample q.primary_open q.primary_support

def OriginalProtectedCommonPrimaryData.smooth_inputs
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ}
    {mu Mb R buffer kappa : ℝ}
    (q : OriginalProtectedCommonPrimaryData Data theta mu Mb R buffer kappa)
    (hs : IncrementsOriginalSmoothInputs Data) :
    IncrementsOriginalSmoothInputs (localPrimaryData Data q.parameterOpen q.primaryDomain) :=
  localPrimaryData_smooth_inputs Data hs q.parameterOpen q.primaryDomain
    (subset_closure.trans q.parameter_closure)
    (fun nu z hz => (q.primary_closure nu (subset_closure hz)).1)

/-- This is the actual counted packet on the same finite local datum, at
the prescribed half-buffer and unchanged common phase constants. -/
theorem OriginalProtectedCommonPrimaryData.exists_counted_supply
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ}
    {mu Mb R buffer kappa : ℝ}
    (q : OriginalProtectedCommonPrimaryData Data theta mu Mb R buffer kappa)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i)) :
    ∃ supply : OriginalCountedPrimarySupply
        (localPrimaryData Data q.parameterOpen q.primaryDomain) theta,
      (∀ nu i, supply.mu nu i = mu) ∧
      (∀ nu i, supply.Mb nu i = Mb) ∧
      (∀ nu i, supply.buffer nu i = buffer/2) ∧
      (∀ nu i, supply.radius nu i = R) ∧
      (∀ nu i a, (supply.packet.piece nu i a).Bnative = 2*(1+2*Mb)) :=
  q.geometry.exists_counted_supply _ (q.domain_conditions hd) (q.smooth_inputs hs) theta
    hCompact hSmooth q.parent_support mu Mb R (buffer/2)

/-- Original kernel bounds restrict to the genuine local domains while
their original physical operator and phase covector remain literal. -/
theorem original_primary_kernel_localization
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hV : V ⊆ Data.parameterOpen) (hDomain : ∀ nu, domain nu ⊆ Data.primaryDomain nu)
    (kappa : ℝ)
    (kernel : RepairOriginalPrimaryKernelInputs Data (actualOriginalNativeOpen Data) kappa) :
    RepairOriginalPrimaryKernelInputs (localPrimaryData Data V domain)
      (actualOriginalNativeOpen (localPrimaryData Data V domain)) kappa := by
  constructor
  intro nu i z hz hActive w
  have hOpen := (round3Parameter_originalNativeOpen_iff (localPrimaryData Data V domain) i z).mp hz
  have hzOld : z ∈ actualOriginalNativeOpen Data i :=
    (round3Parameter_originalNativeOpen_iff Data i z).mpr
      ⟨hOpen.1,hOpen.2.1,hV hOpen.2.2⟩
  exact kernel.lower nu i z hzOld (hDomain nu hActive) w

/-- Construct the protected finite datum from original geometry. The
input geometry is itself manufactured by the actual factory theorem;
this internal step retains it through the needed all-order localization. -/
theorem original_common_geometry_protected_finiteness
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hParent : ∀ i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1)
    (mu Mb R buffer kappa : ℝ)
    (g : OriginalCommonPrimaryGeometry Data theta mu Mb R buffer)
    (kernel : RepairOriginalPrimaryKernelInputs Data (actualOriginalNativeOpen Data) kappa) :
    Nonempty (OriginalProtectedCommonPrimaryData Data theta mu Mb R buffer kappa) := by
  let carrier := fun nu i => originalNativePrimaryCarrier Data i nu
    (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
  have hCarrier : ∀ nu i, IsCompact (carrier nu i) := by
    intro nu i
    have hN := round3Parameter_native_compact_parent (Data.parameterChart i.2)
      (hd.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth i)
      (fun z hz => ⟨(hParent i hz).1.1,mem_univ _⟩)
    apply originalNativePrimaryCarrier_isCompact Data i nu _ hN.2.1
    intro y hy
    obtain ⟨z,hz,rfl⟩ := hN.2.2 hy
    exact ⟨(Data.parameterChart i.2).map_source (hParent i hz).1.1,
      Data.atlas.inner_subset i.1 (hParent i hz).2⟩
  obtain ⟨V,domain,hV,hKV,hVU,hVC,hOpen,hClosedCompact,hClosure,hSupport,hParentLocal,
      hThickening,hBall,hFinite⟩ :=
    original_parent_buffer_preserving_given_finiteness buffer g.buffer_pos Data hd hs hLinear
      Parameter Spatial hParameter hSpatial transition theta hCompact hParent carrier hCarrier
      (fun nu i x hx => (g.buffered nu i x hx).trans (g.native nu i))
  let localData := localPrimaryData Data V domain
  let hdLocal := localPrimaryData_domain_conditions Data hd V domain hV hKV hOpen hSupport
  have hLocalGeometry : OriginalCommonPrimaryGeometry localData theta mu Mb R (buffer/2) := {
    mu_pos := g.mu_pos
    Mb_nonneg := g.Mb_nonneg
    radius_pos := g.radius_pos
    buffer_pos := half_pos g.buffer_pos
    region := fun nu i => g.region nu i ∩ actualOriginalPrimaryNativeOpen localData nu i
    open_region := fun nu i => (g.open_region nu i).inter
      (actualOriginalPrimaryNativeOpen_isOpen localData hdLocal nu i)
    native := fun _ _ _ hz => hz.2
    radius := g.radius
    buffered := fun nu i x hx y hy =>
      ⟨g.buffered nu i x hx ((ball_subset_ball (half_lt_self g.buffer_pos).le) hy),
        hBall nu i x hx hy⟩
    noncritical := g.noncritical
    first := fun nu i x hx => g.first nu i x hx.1
    second := fun nu i x hx =>
      (mul_le_mul_of_nonneg_right (half_lt_self g.buffer_pos).le (norm_nonneg _)).trans
        (g.second nu i x hx.1) }
  exact ⟨{
    parameterOpen := V
    primaryDomain := domain
    parameter_open := hV
    parameter_sample := hKV
    parameter_closure := hVU
    parameter_compact := hVC
    primary_open := hOpen
    primary_compact := hClosedCompact
    primary_closure := hClosure
    primary_support := hSupport
    parent_support := hParentLocal
    geometry := hLocalGeometry
    kernel := original_primary_kernel_localization Data V domain (subset_closure.trans hVU)
      (fun nu z hz => (hClosure nu (subset_closure hz)).1) kappa kernel
    given_finite := hFinite }⟩

end GlobalEmbedding.Continuation.OriginalIncrements

#print axioms GlobalEmbedding.Continuation.OriginalIncrements.OriginalProtectedCommonPrimaryData.exists_counted_supply
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_primary_kernel_localization
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_common_geometry_protected_finiteness
