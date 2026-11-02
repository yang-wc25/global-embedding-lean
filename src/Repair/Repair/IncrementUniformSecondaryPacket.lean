import Repair.IncrementUniformSecondaryProfile
import Probes.Round3PreparedParameterSecondaryPieces
import Probes.Round3PreparedParameterOriginalRawFactory

/-!
# The same full signed-secondary packet with one numerical reserve

The geometry below uses the dominant source chart, which may differ from
the parent host of the secondary piece.  The actual chart transition and
its differential remain explicit.  No transverse-frame lower bound is an
input: it is proved from the uniform numerical template margin.

Replacing the reserve preserves every actual chart, slice, cutoff,
carrier, partition and local multiplicity.  The resulting packet is the
literal input to the existing stable-family and raw-solver factories.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology TensorProduct Classical ENNReal BigOperators
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule

private local instance uniformPacketRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private local instance uniformPacketSquareNormed {E : Type*}
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
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

variable {K : Set ((SymmetricSquare (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
  EuclideanSpace ℝ (Fin N)) × (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ))}

/-- Primitive actual dominant-chart geometry on a reference piece.  All
reserves are constructed from these source data, not included as fields. -/
structure IncrementSecondaryDominantChart
    (C : UniformActualGoodDictionaryCover K) (R J : ℝ)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Ref hd hs i r W) where
  host : Ep → OpenPartialHomeomorph M D
  host_mem : ∀ p, host p ∈ IsManifold.maximalAtlas 𝓙 ∞ M
  domain : Set X
  domain_open : IsOpen domain
  joint_smooth : ContDiffOn ℝ ∞
    (fun z : X => actualOriginalOpenParameterSlice Ref i z.1 ((host z.1).symm z.2)) domain
  transition_smooth : ContDiffOn ℝ ∞ (actualSourceChartTransition host piece.slices) piece.native.target
  transition_maps : MapsTo (actualSourceChartTransition host piece.slices) piece.native.target domain
  coordinates : ∀ z ∈ piece.native.target,
    z.2 ∈ (piece.slices z.1).target ∧ (piece.slices z.1).symm z.2 ∈ (host z.1).source
  actual : ∀ z ∈ piece.native.target, ∃ A : D ≃L[ℝ] D,
    A.toContinuousLinearMap = actualJointSpatialJacobian (actualSourceChartTransition host piece.slices) z ∧
    ‖A.symm.toContinuousLinearMap‖^2 ≤ J ∧
    ‖round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Ref i) host
      (actualSourceChartTransition host piece.slices z)‖ ≤ R ∧
    ∃ t : C.indices, ∃ a : EdgePair (Module.finrank ℝ D+1), ∃ w : ℝ,
      w ≠ 0 ∧
      round4ActualPhaseOperatorInChart (actualOriginalOpenParameterSlice Ref i) host
        (actualSourceChartTransition host piece.slices z) ∈ (C.template t).operatorDomain ∧
      ‖w⁻¹ • actualIncrementCoordinateCovector A - (C.template t).covectors a‖ <
        incrementUniformSignedRadius C R

def incrementUniformSignedReferencePiece
    (C : UniformActualGoodDictionaryCover K) (R J : ℝ) (hJ : 0 < J)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Ref hd hs i r W)
    (geo : IncrementSecondaryDominantChart C R J Ref hd hs i r W piece) :
    Round3PreparedSignedReferencePiece Ref hd hs i r W :=
  { piece with
    cT := incrementSecondaryFrameReserve C R J
    cT_pos := incrementSecondaryFrameReserve_pos C R J hJ
    transverse := by
      intro z hz v
      obtain ⟨A,hA,hJbound,hUpper,t,a,w,hw,hTemplate,hClose⟩ := geo.actual z hz
      exact increment_actual_secondary_frame_reserve C R J hJ
        (actualOriginalOpenParameterSlice Ref i)
        (actualOriginalOpenParameterSlice_contMDiff Ref hd hs i)
        geo.host piece.slices geo.host_mem piece.data.2.2.2.2.1
        piece.native.target geo.domain piece.native.open_target geo.domain_open
        geo.joint_smooth geo.transition_smooth geo.transition_maps geo.coordinates
        z hz A hA hJbound t a w hw hUpper hTemplate hClose v }

/-- The *whole* original secondary packet, including its exact partition,
is retained while its transverse reserve is one numerical constant. -/
def incrementUniformSecondaryPacket
    (C : UniformActualGoodDictionaryCover K) (R J : ℝ) (hJ : 0 < J)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (old : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (geo : ∀ r i a, IncrementSecondaryDominantChart C R J Ref hd hs i r _ (old.piece r i a)) :
    Round3PreparedParameterSecondaryPacket Ref hd hs theta where
  s := old.s
  piece := fun r i a => incrementUniformSignedReferencePiece C R J hJ Ref hd hs i r _
    (old.piece r i a) (geo r i a)
  native_parent := old.native_parent
  smooth := old.smooth
  compact := old.compact
  parent := old.parent
  source := old.source
  partition := old.partition
  count := old.count

theorem increment_uniform_secondary_packet_reserve
    (C : UniformActualGoodDictionaryCover K) (R J : ℝ) (hJ : 0 < J)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (old : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (geo : ∀ r i a, IncrementSecondaryDominantChart C R J Ref hd hs i r _ (old.piece r i a))
    (r) (i) (a) :
    ((incrementUniformSecondaryPacket C R J hJ Ref hd hs theta old geo).piece r i a).cT =
      incrementSecondaryFrameReserve C R J := rfl

theorem increment_uniform_secondary_packet_choice
    (C : UniformActualGoodDictionaryCover K) (R J : ℝ) (hJ : 0 < J)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (old : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (geo : ∀ r i a, IncrementSecondaryDominantChart C R J Ref hd hs i r _ (old.piece r i a))
    (r) (i) (a) :
    round3PreparedParameterSecondaryChoice Ref hd hs i r _
      ((incrementUniformSecondaryPacket C R J hJ Ref hd hs theta old geo).piece r i a) =
    round3PreparedParameterSecondaryChoice Ref hd hs i r _ (old.piece r i a) := rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.incrementUniformSecondaryPacket
#print axioms GlobalEmbedding.Continuation.increment_uniform_secondary_packet_choice
