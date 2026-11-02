import OriginalCollars.ProtectedRegionPrimaryGeometry
import OriginalCollars.NativePrimitiveSignedRegion

/-! Proper compact parameter sets are retained under protected localization.
The two open-slice families agree for every spatial point at each parameter
in the new parameter-open set. This pointwise family identity, not a false
global equality of the parameter domains, transports the actual restricted
second-form operator on the intersected construction region. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation.OriginalIncrements
open FaithfulIncrements OriginalCollars
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance protectedPrimitiveRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance protectedPrimitiveSquareNormed {E : Type*}
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
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

/-- Only membership in the actual new open parameter set is required.
The compact sample K may remain proper or have empty interior. -/
theorem OriginalProtectedRegionPrimaryData.open_slice_eq_at
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ}
    {mu Mb R buffer kappa : ℝ}
    (q : OriginalProtectedRegionPrimaryData Data theta mu Mb R buffer kappa)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (p : Ep)
    (hp : (Data.parameterChart i.2).symm p ∈ q.parameterOpen) :
    actualOriginalOpenParameterSlice
      (localPrimaryData Data q.parameterOpen q.primaryDomain) i p =
      actualOriginalOpenParameterSlice Data i p := by
  rw [actualOriginalOpenParameterSlice_eq
      (localPrimaryData Data q.parameterOpen q.primaryDomain) i p hp,
    actualOriginalOpenParameterSlice_eq Data i p
      (q.parameter_closure (subset_closure hp))]
  rfl

/-- At the same parameter, the true normal projection and spatial
Hessian are unchanged; no comparison of different operator norms occurs. -/
theorem OriginalProtectedRegionPrimaryData.phase_operator_eq_at
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ}
    {mu Mb R buffer kappa : ℝ}
    (q : OriginalProtectedRegionPrimaryData Data theta mu Mb R buffer kappa)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : X)
    (hp : (Data.parameterChart i.2).symm z.1 ∈ q.parameterOpen) :
    round4ActualPhaseOperatorInChart
      (actualOriginalOpenParameterSlice (localPrimaryData Data q.parameterOpen q.primaryDomain) i)
      (fun _ => Data.atlas.chart i.1) z =
    round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Data i)
      (fun _ => Data.atlas.chart i.1) z := by
  exact congrArg (fun f : M → EuclideanSpace ℝ (Fin N) =>
    round4ActualPhaseOperatorInChart (fun _ : Ep => f)
      (fun _ => Data.atlas.chart i.1) z) (q.open_slice_eq_at i z.1 hp)

/-- Intersect the original signed domain with the two protected primary
domains. The same signed carrier retains a common numerical half-buffer,
and all original functions, primitive two-jets and restriction reserves
remain attached to the same local datum. -/
def OriginalProtectedRegionPrimaryData.protect_native_primitive_signed_region
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ}
    {primaryMu primaryMb primaryR primaryBuffer primaryKernel : ℝ}
    (q : OriginalProtectedRegionPrimaryData Data theta
      primaryMu primaryMb primaryR primaryBuffer primaryKernel)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (mu R buffer coordinateBound kernel lower nativeTwo : ℝ) (Phase : ℕ → ℝ)
    (old : NativePrimitiveSignedRegion Data i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
      mu R buffer coordinateBound kernel lower nativeTwo Phase) :
    NativePrimitiveSignedRegion (localPrimaryData Data q.parameterOpen q.primaryDomain) i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
      mu R (min buffer (primaryBuffer/2)) coordinateBound kernel lower nativeTwo Phase := by
  let localData := localPrimaryData Data q.parameterOpen q.primaryDomain
  let carrier := (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)) ''
    (tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ∩
      actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2
        ((Data.parameterChart i.2).target ×ˢ (univ : Set M)))
  have hFirst : carrier ⊆ originalNativePrimaryCarrier localData i r.val.1.1
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) := by
    rintro z ⟨y,hy,rfl⟩
    exact ⟨y,⟨hy.1,hy.2.1⟩,rfl⟩
  have hSecond : carrier ⊆ originalNativePrimaryCarrier localData i r.val.1.2
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) := by
    rintro z ⟨y,hy,rfl⟩
    exact ⟨y,⟨hy.1,hy.2.2⟩,rfl⟩
  refine {
    domain := old.domain ∩ (q.geometry.region r.val.1.1 i ∩ q.geometry.region r.val.1.2 i)
    center := old.center
    isOpen := old.isOpen.inter ((q.geometry.open_region _ _).inter (q.geometry.open_region _ _))
    carrier_radius := old.carrier_radius
    carrier_buffer := ?_
    target := fun z hz => old.target hz.1
    parent := fun z hz => old.parent hz.1
    active := fun z hz => ⟨q.geometry.native _ _ hz.2.1,q.geometry.native _ _ hz.2.2⟩
    inner := fun z hz => old.inner z hz.1
    native_first := fun z hz => old.native_first z hz.1
    native_jets := fun k hk z hz => old.native_jets k hk z hz.1
    coordinates := fun z hz => old.coordinates z hz.1
    phase_smooth := old.phase_smooth.mono inter_subset_left
    phase_noncritical := old.phase_noncritical
    phase_jets := fun j z hz => old.phase_jets j z hz.1
    original_kernel := ?_ }
  · intro z hz y hy
    exact ⟨old.carrier_buffer z hz ((ball_subset_ball (min_le_left _ _)) hy),
      q.geometry.buffered _ _ z (hFirst hz) ((ball_subset_ball (min_le_right _ _)) hy),
      q.geometry.buffered _ _ z (hSecond hz) ((ball_subset_ball (min_le_right _ _)) hy)⟩
  · intro y hy v
    have hNative : y ∈ actualOriginalNativeOpen localData i :=
      round3_prepared_primary_native_subset localData i r.val.1.1
        (q.geometry.native _ _ hy.2.1)
    have hp := actualOriginalNativeOpen_parameter localData i hNative
    change kernel*‖v‖ ≤ ‖covectorRestriction
      (round4ActualPhaseOperatorInChart
        (actualOriginalOpenParameterSlice (localPrimaryData Data q.parameterOpen q.primaryDomain) i)
        (fun _ => Data.atlas.chart i.1) y)
      (fderiv ℝ (fun x : D => actualOriginalParameterSignedPhase Data i r.val
        (y.1,(Data.atlas.chart i.1).symm x)) y.2) v‖
    rw [q.phase_operator_eq_at i y hp]
    exact old.original_kernel y hy.1 v

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.OriginalProtectedRegionPrimaryData.open_slice_eq_at
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.OriginalProtectedRegionPrimaryData.phase_operator_eq_at
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.OriginalProtectedRegionPrimaryData.protect_native_primitive_signed_region
