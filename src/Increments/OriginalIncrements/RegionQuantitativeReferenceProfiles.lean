import OriginalIncrements.QuantitativeReferenceProfiles
import OriginalIncrements.OriginalFinitePrimarySupply
import Repair.EntranceSpatialPrimaryBudget

/-!
# Region-local original kernel margins condition the actual primary grid

Only each genuine construction region supplies its chosen-phase lower
bound. The actual grid records native.source containment, and the true
reference restriction preserves that containment. There is no requirement
for a common margin on an unused part of an old primary domain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule

private local instance regionQuantitativeReferenceRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance regionQuantitativeReferenceSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)

/-- Transport of the numerical original kernel reserve to this same chart.
The source/target restrictions are actual constructor outputs, not an extra
assumption equating partial-homeomorphism domains. -/
theorem original_budgeted_region_restricted_transverse
    [T2Space M]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalIncrements.OriginalBudgetedPrimarySupply Data theta)
    (geometry : RestrictedReferenceGeometry Data hd hs theta budgeted.packet)
    (Mb kappa : ℝ) (hMb : 0 ≤ Mb) (hkappa : 0 < kappa)
    (hMbBound : ∀ nu i, budgeted.Mb nu i ≤ Mb)
    (O : Fin Data.primaryCount → Fin Data.atlas.count × Fin Data.parameterCount → Set X)
    (hPieceRegion : ∀ nu i a, (budgeted.packet.piece nu i a).native.source ⊆ O nu i)
    (kernel : ∀ nu i z, z ∈ O nu i → ∀ w, kappa*‖w‖ ≤ ‖covectorRestriction
      (round4ActualPhaseOperatorInChart
        (fun p x => Data.F ((Data.parameterChart i.2).symm p,x))
        (fun _ => Data.atlas.chart i.1) z)
      (fderiv ℝ (fun x : D => Data.phase nu
        ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm x)) z.2) w‖) :
    ∀ nu i a z, z ∈ (geometry.piece nu i a).native.target → ∀ v : Tdata,
      (kappa/((2*(1+2*Mb))^2*actualIncrementSortedSymmetricConstant m))^2*‖v‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame
          (actualOriginalOpenParameterSlice Data i z.1)
          (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
          ((geometry.piece nu i a).slices z.1).symm z.2 v‖^2 := by
  intro nu i a z hz v
  let piece := geometry.piece nu i a
  let F := actualOriginalOpenParameterSlice Data i
  let host := Data.atlas.chart piece.host
  have hB : 0 < 2*(1+2*Mb) := by positivity
  have hJoint : ContDiffOn ℝ ∞ (fun y : X => F y.1 (host.symm y.2))
      (actualOriginalNativeOpen Data (piece.host,i.2)) :=
    actualOriginalOpenParameterSlice_native_contDiffOn Data hd hs (piece.host,i.2)
  have hForward (y : X) (hy : y ∈ piece.native.source) :
      ‖fderiv ℝ piece.native y‖ ≤ 2*(1+2*Mb) := by
    change ‖fderiv ℝ (geometry.piece nu i a).native y‖ ≤ _
    rw [geometry.forward nu i a]
    exact (budgeted.native_first nu i a y (geometry.source_subset nu i a hy)).trans (by
      have hh := hMbBound nu i
      nlinarith)
  have hMargin : ∀ w, kappa*‖w‖ ≤ ‖covectorRestriction
      (round4ActualPhaseOperatorInChart F (fun _ => host) (piece.native.symm z))
      (fderiv ℝ (fun x : D => Data.phase nu
        ((Data.parameterChart i.2).symm (piece.native.symm z).1,host.symm x))
        (piece.native.symm z).2) w‖ := by
    have hy := piece.native.map_target hz
    have hNative := piece.native_source hy
    have hActive := prepared_primary_native_source_active Data i nu _ piece _ hy
    have hOpen := actualOriginalNativeOpen_parameter Data (piece.host,i.2) hNative
    have hSlice : F (piece.native.symm z).1 =
        fun x => Data.F ((Data.parameterChart i.2).symm (piece.native.symm z).1,x) :=
      actualOriginalOpenParameterSlice_eq Data i (piece.native.symm z).1 hOpen
    have hHost : piece.host = i.1 :=
      (geometry.host nu i a).trans (budgeted.packet.host nu i a)
    let Bound (h : Fin Data.atlas.count) : Prop :=
      ∀ w, kappa*‖w‖ ≤ ‖covectorRestriction
        (round4ActualPhaseOperatorInChart F (fun _ => Data.atlas.chart h) (piece.native.symm z))
        (fderiv ℝ (fun x : D => Data.phase nu
          ((Data.parameterChart i.2).symm (piece.native.symm z).1,(Data.atlas.chart h).symm x))
          (piece.native.symm z).2) w‖
    have hAt : Bound i.1 := by
      intro w
      have hh := kernel nu i _ (hPieceRegion nu i a (geometry.source_subset nu i a hy)) w
      simpa only [round4ActualPhaseOperatorInChart,actualNormalHessianInChart,hSlice] using hh
    change Bound piece.host
    exact (congrArg Bound hHost).mpr hAt
  exact repairEntrance_native_original_transverse_reserve F
    (actualOriginalOpenParameterSlice_contMDiff Data hd hs i) host
    (hd.atlas_smooth.chart_mem piece.host) piece.native _ piece.slices piece.data
    (actualOriginalNativeOpen Data (piece.host,i.2))
    (actualOriginalNativeOpen_isOpen Data hd (piece.host,i.2)) hJoint piece.native_source
    kappa (2*(1+2*Mb)) hkappa.le hB hForward z hz hMargin v

/-- The actual constructed reference record uses the explicit reserve. All
its chart functions, partial domains, slice inverses and cutoffs stay those
of the retained restricted geometry. -/
theorem original_budgeted_reference_profiles_from_region_kernel
    [T2Space M]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (budgeted : OriginalIncrements.OriginalBudgetedPrimarySupply Data theta)
    (hInner : ∀ nu i a y, y ∈ tsupport (budgeted.packet.piece nu i a).cutoff →
      y.2 ∈ Data.atlas.inner (budgeted.packet.piece nu i a).host)
    (Mb kappa : ℝ) (hMb : 0 ≤ Mb) (hkappa : 0 < kappa)
    (hMbBound : ∀ nu i, budgeted.Mb nu i ≤ Mb)
    (O : Fin Data.primaryCount → Fin Data.atlas.count × Fin Data.parameterCount → Set X)
    (hPieceRegion : ∀ nu i a, (budgeted.packet.piece nu i a).native.source ⊆ O nu i)
    (kernel : ∀ nu i z, z ∈ O nu i → ∀ w, kappa*‖w‖ ≤ ‖covectorRestriction
      (round4ActualPhaseOperatorInChart
        (fun p x => Data.F ((Data.parameterChart i.2).symm p,x))
        (fun _ => Data.atlas.chart i.1) z)
      (fderiv ℝ (fun x : D => Data.phase nu
        ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm x)) z.2) w‖) :
    ∃ geometry : RestrictedReferenceGeometry Data hd hs theta budgeted.packet,
      geometry.cT =
        (kappa/((2*(1+2*Mb))^2*actualIncrementSortedSymmetricConstant m))^2 := by
  obtain ⟨old⟩ := original_open_restricted_reference_profiles Data hd hs hp hImm
    theta budgeted.packet hInner
  have hB : 0 < 2*(1+2*Mb) := by positivity
  let geometry : RestrictedReferenceGeometry Data hd hs theta budgeted.packet := {
    old with
    cT := (kappa/((2*(1+2*Mb))^2*actualIncrementSortedSymmetricConstant m))^2
    cT_pos := sq_pos_of_pos (div_pos hkappa (mul_pos (sq_pos_of_pos hB)
      (actualIncrementSortedSymmetricConstant_pos m)))
    transverse := original_budgeted_region_restricted_transverse Data hd hs theta budgeted old
      Mb kappa hMb hkappa hMbBound O hPieceRegion kernel }
  exact ⟨geometry,rfl⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.original_budgeted_region_restricted_transverse
#print axioms GlobalEmbedding.Continuation.original_budgeted_reference_profiles_from_region_kernel
