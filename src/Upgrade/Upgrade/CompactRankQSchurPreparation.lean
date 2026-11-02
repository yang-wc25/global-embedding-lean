import Upgrade.CompactRankQPreparation
import Upgrade.CompactNormalizedTensors
import Upgrade.RankQSchurMargin

/-!
# Full weight-independent Schur neighborhood preparation

The fixed principal margin first determines a tensor bound and a tolerance
for the derivative of the actual Schur equation. The resulting actual form
ball and spatial neighborhood are selected before weights. Later weight
simulation multiplies only the raw probe error; the geometric derivative
error is bounded separately by delta times the fixed tensor bound.
-/

noncomputable section
open Set Filter Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
attribute [local instance] rankQResidualNormedAddCommGroup rankQResidualNormedSpace
attribute [local instance] rankQResidualFiniteDimensional

/-- The already proved Schur margin, stored at its native generic types to
avoid repeatedly elaborating nested actual normal-space norm instances. -/
structure PreparedSchurBall
    {S W : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [FiniteDimensional ℝ S] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (B : S →L[ℝ] W) (delta : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  spec : ∀ C : S →L[ℝ] W, ‖C - B‖ < radius →
    (rankQBlockA B C).IsInvertible ∧ ContDiffAt ℝ ∞ (rankQSchur B) C ∧
    ‖fderiv ℝ (rankQSchur B) C - rankQNormalBlock B‖ < delta ∧
    ‖fderiv ℝ (rankQSchur B) C‖ ≤ ‖rankQNormalBlock B‖ + delta ∧
    (rankQSchur B C = 0 ↔ finrank ℝ C.range = finrank ℝ B.range)

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

structure RankQSchurPreparedNeighborhood
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (packet : RankQLocalWavePacket F hF x y)
    (i : Fin A.count) (hx : x ∈ interior (A.support i)) where
  principal : RankQPreparedNeighborhood A hA packet i hx
  tensorBound : ℝ
  tensorBound_pos : 0 < tensorBound
  derivativeTolerance : ℝ
  derivativeTolerance_pos : 0 < derivativeTolerance
  derivative_budget : derivativeTolerance * tensorBound ≤ principal.tolerance / 4
  formBall : PreparedSchurBall (rankQActualReference F hF x) derivativeTolerance
  neighborhood : Set (M × M)
  neighborhood_open : IsOpen neighborhood
  center_mem : (x, y) ∈ neighborhood
  subset_principal : neighborhood ⊆ principal.neighborhood
  tensor_bound : ∀ z ∈ neighborhood, ∀ l,
    ‖(normalSpace (I := IM) F x).orthogonalProjectionOnto.comp
        (probeTensorInFrame
          (probeAtlasNormalizedFrame A hA i x (hA.support_subset i (interior_subset hx)) z.1)
          ((packet.waves l).tensor z.1))‖ ≤ tensorBound
  reference_variation : ∀ z ∈ neighborhood,
    ‖normalizedReferenceForm A hA F i x (hA.support_subset i (interior_subset hx)) z.1 -
      rankQActualReference F hF x‖ < formBall.radius / 2
  normal_gap : ∀ z ∈ neighborhood,
    ‖(normalSpace (I := IM) F z.1).starProjection -
      (normalSpace (I := IM) F x).starProjection‖ < 1 / 2

theorem RankQLocalWavePacket.exists_schur_prepared_neighborhood [T2Space M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (packet : RankQLocalWavePacket F hF x y)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    (hrank : finrank ℝ (trueSecondForm F hF x).range = n * (n - 1) / 2)
    (i : Fin A.count) (hx : x ∈ interior (A.support i)) :
    Nonempty (RankQSchurPreparedNeighborhood A hA packet i hx) := by
  classical
  obtain ⟨principal⟩ := packet.exists_prepared_neighborhood A hA (himm x) hphase hn hN hrank i hx
  obtain ⟨L, hL, U, hU, hxU, _, hbound⟩ :=
    exists_finite_normalized_tensor_bound packet.waves A hA i x hx
  let delta := principal.tolerance / (4 * (L + 1))
  have hdelta : 0 < delta := div_pos principal.tolerance_pos (by positivity)
  have hbudget : delta * L ≤ principal.tolerance / 4 := by
    have heq : delta * (L + 1) = principal.tolerance / 4 := by
      dsimp only [delta]
      field_simp
    nlinarith [hdelta.le]
  obtain ⟨rho, hrho, hmargin⟩ := rankQSchur_exists_margin (rankQActualReference F hF x) delta hdelta
  let ball : PreparedSchurBall (rankQActualReference F hF x) delta := ⟨rho, hrho, hmargin⟩
  obtain ⟨W, hW, hxW, _, hreference, hnormal⟩ :=
    exists_normalizedReference_neighborhood A hA F hF himm i x hx
      (show 0 < rho / 2 by positivity)
  exact ⟨{
    principal := principal
    tensorBound := L
    tensorBound_pos := hL
    derivativeTolerance := delta
    derivativeTolerance_pos := hdelta
    derivative_budget := hbudget
    formBall := ball
    neighborhood := principal.neighborhood ∩ Prod.fst ⁻¹' (U ∩ W)
    neighborhood_open := principal.neighborhood_open.inter ((hU.inter hW).preimage continuous_fst)
    center_mem := ⟨principal.center_mem, hxU, hxW⟩
    subset_principal := inter_subset_left
    tensor_bound := fun z hz l ↦ hbound z.1 hz.2.1 l
    reference_variation := fun z hz ↦ hreference z.1 hz.2.2
    normal_gap := fun z hz ↦ hnormal z.1 hz.2.2 }⟩

end GlobalEmbedding.Upgrade
