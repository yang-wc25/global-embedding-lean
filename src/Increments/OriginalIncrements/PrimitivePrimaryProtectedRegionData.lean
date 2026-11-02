import OriginalCollars.ProtectedRegionPrimaryGeometry

/-!
# Primitive chosen-primary bounds construct the protected actual datum

The inputs are open domains and bounds for the original literal phase
and its spatial restriction operator. No adapted chart, inverse, grid,
primary supply, protected datum, finite norm or solver is supplied. The
same original compact parameter set is retained, with no full-P premise.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements
open OriginalCollars FaithfulIncrements
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)

theorem primitive_primary_protected_region_data
    (mu Mb R buffer kappa : ℝ)
    (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hR : 0 < R) (hbuffer : 0 < buffer)
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
    (O : Fin Data.primaryCount → Fin Data.atlas.count × Fin Data.parameterCount → Set (Ep × D))
    (hO : ∀ nu i, IsOpen (O nu i))
    (hNative : ∀ nu i, O nu i ⊆ actualOriginalPrimaryNativeOpen Data nu i)
    (hRadius : ∀ nu i, originalNativePrimaryCarrier Data i nu
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ⊆ closedBall 0 R)
    (hBuffer : ∀ nu i x, x ∈ originalNativePrimaryCarrier Data i nu
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) → ball x buffer ⊆ O nu i)
    (hNoncritical : ∀ nu i x, x ∈ originalNativePrimaryCarrier Data i nu
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) →
      mu ≤ ‖(fderiv ℝ (originalNativePrimaryPhase Data nu i) x).comp
        (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hFirst : ∀ nu i x, x ∈ O nu i → ‖fderiv ℝ (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb)
    (hSecond : ∀ nu i x, x ∈ O nu i →
      buffer*‖iteratedFDeriv ℝ 2 (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb)
    (kernel : OriginalRegionPrimaryKernelInputs Data O kappa) :
    Nonempty (OriginalProtectedRegionPrimaryData Data theta mu Mb R buffer kappa) := by
  let geometry : OriginalCommonPrimaryGeometry Data theta mu Mb R buffer := {
    mu_pos := hmu
    Mb_nonneg := hMb
    radius_pos := hR
    buffer_pos := hbuffer
    region := O
    open_region := hO
    native := hNative
    radius := hRadius
    buffered := hBuffer
    noncritical := hNoncritical
    first := hFirst
    second := hSecond }
  exact original_region_geometry_protected_finiteness Data hd hs hLinear
    Parameter Spatial hParameter hSpatial transition theta hCompact hSmooth hParent
    mu Mb R buffer kappa geometry kernel

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.primitive_primary_protected_region_data
