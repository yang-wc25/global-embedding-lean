import OriginalCollars.ProtectedCommonGeometryPacket
import FaithfulRepair.ProtectedParentGivenFiniteness

/-!
# Protected common primary geometry with only region-local kernel margins

The same original carriers, half-buffer, whole parent supports and finite
Given profiles are preserved. The kernel field is only on each actual
construction region, where the corresponding chosen phase is used. It
makes no assertion on unused portions of the old primary domains.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology ENNReal TensorProduct
namespace GlobalEmbedding.Continuation.OriginalIncrements
open FaithfulIncrements FaithfulRepair OriginalCollars
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance protectedRegionRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance protectedRegionSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

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

/-- The actual chosen-phase restriction reserve only on its own primitive
construction region; inactive old primary-domain points are not quantified. -/
structure OriginalRegionPrimaryKernelInputs
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (O : Fin Data.primaryCount → Fin Data.atlas.count × Fin Data.parameterCount → Set X)
    (kappa : ℝ) : Prop where
  lower : ∀ nu i z, z ∈ O nu i → ∀ w, kappa*‖w‖ ≤ ‖covectorRestriction
    (round4ActualPhaseOperatorInChart
      (fun p x => Data.F ((Data.parameterChart i.2).symm p,x))
      (fun _ => Data.atlas.chart i.1) z)
    (fderiv ℝ (fun x : D => Data.phase nu
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm x)) z.2) w‖

/-- An actual internal localization of the original datum. The numerical
geometry, original kernel reserve, parent, and finite profiles all belong
to the identical local datum displayed in the fields. -/
structure OriginalProtectedRegionPrimaryData
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
  kernel : OriginalRegionPrimaryKernelInputs (localPrimaryData Data parameterOpen primaryDomain)
    geometry.region kappa
  given_finite : ∀ j ell,
    actualOriginalGivenInputProfile (localPrimaryData Data parameterOpen primaryDomain) j ell ≠ ⊤

def OriginalProtectedRegionPrimaryData.domain_conditions
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ}
    {mu Mb R buffer kappa : ℝ}
    (q : OriginalProtectedRegionPrimaryData Data theta mu Mb R buffer kappa)
    (hd : IncrementsOriginalDomainConditions Data) :
    IncrementsOriginalDomainConditions (localPrimaryData Data q.parameterOpen q.primaryDomain) :=
  localPrimaryData_domain_conditions Data hd q.parameterOpen q.primaryDomain q.parameter_open
    q.parameter_sample q.primary_open q.primary_support

def OriginalProtectedRegionPrimaryData.smooth_inputs
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ}
    {mu Mb R buffer kappa : ℝ}
    (q : OriginalProtectedRegionPrimaryData Data theta mu Mb R buffer kappa)
    (hs : IncrementsOriginalSmoothInputs Data) :
    IncrementsOriginalSmoothInputs (localPrimaryData Data q.parameterOpen q.primaryDomain) :=
  localPrimaryData_smooth_inputs Data hs q.parameterOpen q.primaryDomain
    (subset_closure.trans q.parameter_closure)
    (fun nu z hz => (q.primary_closure nu (subset_closure hz)).1)

/-- This is the actual counted packet on the same finite local datum, at
the prescribed half-buffer and unchanged common phase constants. -/
theorem OriginalProtectedRegionPrimaryData.exists_counted_supply
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ}
    {mu Mb R buffer kappa : ℝ}
    (q : OriginalProtectedRegionPrimaryData Data theta mu Mb R buffer kappa)
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

/-- Construct the protected finite datum from original geometry. The
input geometry is itself manufactured by the actual factory theorem;
this internal step retains it through the needed all-order localization. -/
theorem original_region_geometry_protected_finiteness
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
    (kernel : OriginalRegionPrimaryKernelInputs Data g.region kappa) :
    Nonempty (OriginalProtectedRegionPrimaryData Data theta mu Mb R buffer kappa) := by
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
  let hLocalGeometry : OriginalCommonPrimaryGeometry localData theta mu Mb R (buffer/2) := {
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
    kernel := by
      constructor
      intro nu i z hz w
      change z ∈ g.region nu i ∩ actualOriginalPrimaryNativeOpen localData nu i at hz
      exact kernel.lower nu i z hz.1 w
    given_finite := hFinite }⟩

end GlobalEmbedding.Continuation.OriginalIncrements

#print axioms GlobalEmbedding.Continuation.OriginalIncrements.OriginalProtectedRegionPrimaryData.exists_counted_supply
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_region_geometry_protected_finiteness
