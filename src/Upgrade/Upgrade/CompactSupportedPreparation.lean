import Upgrade.CompactNormalizedReference
import Upgrade.CompactNormalizedTensors
import Upgrade.SupportedSourcePackets
import Upgrade.SupportedEquationStability

/-!
# Spatial preparation of an actual supported source packet

The supported equation and independent normal columns come from the accepted
strong supported-rank construction. This module selects their positive
operator tolerance and actual source neighborhood before finite concatenation
and before the probes provider chooses a parameter space or weights.
-/

noncomputable section
open Set Filter Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

structure SupportedPreparedNeighborhood
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (packet : SupportedLocalWavePacket F hF x y)
    (i : Fin A.count) (hx : x ∈ interior (A.support i)) where
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  equation_stability : ∀ (C : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F x)
      (T : Fin (n * (n - 1) / 2) → SymmetricSquare E →L[ℝ] normalSpace (I := IM) F x),
    ‖C - LinearMap.toContinuousLinearMap
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x)‖ < tolerance →
    (∀ l, ‖T l - (normalSpace (I := IM) F x).orthogonalProjectionOnto.comp
      ((packet.waves l).tensor x)‖ < tolerance) →
    C ∈ packet.chart.domain ∧ LinearIndependent ℝ
      (fun l ↦ fderiv ℝ packet.chart.equation C (T l))
  neighborhood : Set M
  neighborhood_open : IsOpen neighborhood
  center_mem : x ∈ neighborhood
  support : neighborhood ⊆ interior (A.support i)
  cutoff : ∀ z ∈ neighborhood, ∀ l, (packet.waves l).cutoff z = 1
  tensor_variation : ∀ z ∈ neighborhood, ∀ l,
    ‖(normalSpace (I := IM) F x).orthogonalProjectionOnto.comp
        (probeTensorInFrame
          (probeAtlasNormalizedFrame A hA i x (hA.support_subset i (interior_subset hx)) z)
          ((packet.waves l).tensor z)) -
      (normalSpace (I := IM) F x).orthogonalProjectionOnto.comp ((packet.waves l).tensor x)‖ <
      tolerance / 16
  reference_variation : ∀ z ∈ neighborhood,
    ‖normalizedReferenceForm A hA F i x (hA.support_subset i (interior_subset hx)) z -
      LinearMap.toContinuousLinearMap
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x)‖ <
      tolerance / 4
  normal_gap : ∀ z ∈ neighborhood,
    ‖(normalSpace (I := IM) F z).starProjection -
      (normalSpace (I := IM) F x).starProjection‖ < 1 / 2

/-- The geometry itself supplies the tolerance and the fixed neighborhood;
none is assumed to be available from the later probe family. -/
theorem SupportedLocalWavePacket.exists_prepared_neighborhood [T2Space M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (packet : SupportedLocalWavePacket F hF x y)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (i : Fin A.count) (hx : x ∈ interior (A.support i)) :
    Nonempty (SupportedPreparedNeighborhood A hA packet i hx) := by
  classical
  let T := fun l ↦ (normalSpace (I := IM) F x).orthogonalProjectionOnto.comp
    ((packet.waves l).tensor x)
  obtain ⟨delta, hdelta, hstable⟩ :=
    supported_equation_finite_column_tolerance packet.chart T packet.normal_columns
  obtain ⟨U, hU, hxU, hUsupport, hlead⟩ :=
    exists_finite_normalized_tensor_neighborhood packet.waves A hA i x hx
      (show 0 < delta / 16 by positivity)
  obtain ⟨W, hW, hxW, _, hreference, hnormal⟩ :=
    exists_normalizedReference_neighborhood A hA F hF himm i x hx
      (show 0 < delta / 4 by positivity)
  obtain ⟨Ucut, hUcutsub, hUcut, hxUcut⟩ := mem_nhds_iff.mp packet.one_near
  refine ⟨{
    tolerance := delta
    tolerance_pos := hdelta
    equation_stability := hstable
    neighborhood := U ∩ W ∩ Ucut
    neighborhood_open := (hU.inter hW).inter hUcut
    center_mem := ⟨⟨hxU, hxW⟩, hxUcut⟩
    support := fun z hz ↦ hUsupport hz.1.1
    cutoff := fun z hz l ↦ hUcutsub hz.2 l
    tensor_variation := fun z hz l ↦ hlead z hz.1.1 l
    reference_variation := fun z hz ↦ hreference z hz.1.2
    normal_gap := fun z hz ↦ hnormal z hz.1.2 }⟩

end GlobalEmbedding.Upgrade
