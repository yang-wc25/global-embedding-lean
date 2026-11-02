import Upgrade.CompactPrincipalNeighborhood
import Upgrade.RankQFixedPacketPrincipal
import Upgrade.RankQResidualNorms

/-!
# Weight-independent actual rank-q neighborhood preparation

The auxiliary weights are fixed to 1 and 2 before any cover or probe call.
The actual packet supplies an independent 2n+1 frame and a positive finite
margin. One actual source/leading-field neighborhood is then selected using
that margin. Later returned probe weights must simulate these fixed columns;
the neighborhoods are never shrunk after that return.
-/

noncomputable section
open Set Filter Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators

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

local instance actualResidualNormedAddCommGroup
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x : M} :
    NormedAddCommGroup
      ((rankQActualReference F hF x).ker →L[ℝ] (rankQActualReference F hF x).rangeᗮ) :=
  rankQResidualNormedAddCommGroup (rankQActualReference F hF x)

local instance actualResidualNormedSpace
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x : M} :
    NormedSpace ℝ
      ((rankQActualReference F hF x).ker →L[ℝ] (rankQActualReference F hF x).rangeᗮ) :=
  rankQResidualNormedSpace (rankQActualReference F hF x)

local instance actualResidualFiniteDimensional
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x : M} :
    FiniteDimensional ℝ
      ((rankQActualReference F hF x).ker →L[ℝ] (rankQActualReference F hF x).rangeᗮ) :=
  rankQResidualFiniteDimensional (rankQActualReference F hF x)

local instance actualJointNorm
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x : M} :
    Norm (((rankQActualReference F hF x).ker →L[ℝ]
      (rankQActualReference F hF x).rangeᗮ) × V) :=
  @Prod.toNorm _ _
    (rankQResidualNormedAddCommGroup (rankQActualReference F hF x)).toNorm inferInstance

/-- Actual principal and source data fixed before weights are returned. The
coefficient budget is exactly the finite-column error accumulation. -/
structure RankQPreparedNeighborhood
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (packet : RankQLocalWavePacket F hF x y)
    (i : Fin A.count) (hx : x ∈ interior (A.support i)) where
  directions : Fin (2 * n + 1) → (((Fin n × Fin 2) → ℝ) × E)
  independent : LinearIndependent ℝ
    (fun j ↦ packet.principalMap rankQPreparationWeights (directions j))
  margin : ℝ
  margin_pos : 0 < margin
  frame_lower : ∀ c : Fin (2 * n + 1) → ℝ, margin * ‖c‖ ≤
    ‖∑ j, c j • packet.principalMap rankQPreparationWeights (directions j)‖
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  coefficient_budget : ∀ j,
    (Fintype.card (Fin n × Fin 2) : ℝ) * tolerance * ‖(directions j).1‖ +
      tolerance * ‖(probeAtlasInverseFrameEquiv A hA i x
        (hA.support_subset i (interior_subset hx))).symm (directions j).2‖ ≤
      margin / (2 * ((2 * n + 1 : ℕ) + 1 : ℝ))
  neighborhood : Set (M × M)
  neighborhood_open : IsOpen neighborhood
  center_mem : (x, y) ∈ neighborhood
  support : ∀ z ∈ neighborhood, z.1 ∈ interior (A.support i)
  cutoff : ∀ z ∈ neighborhood, ∀ l,
    ((packet.waves l).cutoff z.1 = 1 ∧ (packet.waves l).cutoff z.2 = 0)
  principal_variation : ∀ z ∈ neighborhood, ∀ l : Fin n × Fin 2,
    ‖atlasIncidencePrincipal (packet.waves l.1) A hA i x
        (hA.support_subset i (interior_subset hx))
        (normalSpace (I := IM) F x).orthogonalProjectionOnto
        (rankQNormalBlock (rankQActualReference F hF x))
        (rankQPreparationWeights l.1 l.2) (A.chart i z.1) -
      rankQActualPrincipalColumn F hF x ((packet.waves l.1).tensor x)
        (-((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (packet.waves l.1).value x)‖ <
      tolerance / 4
  source_variation : ∀ z ∈ neighborhood,
    ‖probeAtlasFirstJet A F i z.1 - probeAtlasFirstJet A F i x‖ < tolerance / 4

/-- Construct the weight-independent preparation from the actual immersion,
phase condition, rank-q equality and already fixed actual local legal packet.
No desired rank or frame margin of the incidence derivative is an input. -/
theorem RankQLocalWavePacket.exists_prepared_neighborhood [T2Space M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (packet : RankQLocalWavePacket F hF x y)
    (himm : Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    (hrank : finrank ℝ (trueSecondForm F hF x).range = n * (n - 1) / 2)
    (i : Fin A.count) (hx : x ∈ interior (A.support i)) :
    Nonempty (RankQPreparedNeighborhood A hA packet i hx) := by
  classical
  obtain ⟨d, hli⟩ := packet.preparation_principal_frame himm hphase hn hN hrank
  obtain ⟨margin, hm, hframe⟩ := exists_positive_finite_frame_margin
    (fun j ↦ packet.principalMap rankQPreparationWeights (d j)) hli
  let frame := probeAtlasInverseFrameEquiv A hA i x (hA.support_subset i (interior_subset hx))
  obtain ⟨C, hC⟩ := Finite.exists_le (fun j : Fin (2 * n + 1) ↦
    (Fintype.card (Fin n × Fin 2) : ℝ) * ‖(d j).1‖ + ‖frame.symm (d j).2‖)
  let b := margin / (2 * ((2 * n + 1 : ℕ) + 1 : ℝ))
  have hb : 0 < b := div_pos hm (by positivity)
  let eps := b / (|C| + 1)
  have heps : 0 < eps := div_pos hb (by positivity)
  have hbudget (j : Fin (2 * n + 1)) :
      (Fintype.card (Fin n × Fin 2) : ℝ) * eps * ‖(d j).1‖ +
        eps * ‖frame.symm (d j).2‖ ≤ b := by
    calc
      _ = eps * ((Fintype.card (Fin n × Fin 2) : ℝ) * ‖(d j).1‖ +
          ‖frame.symm (d j).2‖) := by ring
      _ ≤ eps * (|C| + 1) := mul_le_mul_of_nonneg_left
        ((hC j).trans ((le_abs_self C).trans (by linarith))) heps.le
      _ = b := div_mul_cancel₀ b (by positivity : |C| + 1 ≠ 0)
  obtain ⟨U, hU, hxU, hUsupport, hprincipal, hsource⟩ :=
    exists_actual_principal_source_neighborhood
      (fun l : Fin n × Fin 2 ↦ packet.waves l.1) A hA i x hx
      (normalSpace (I := IM) F x).orthogonalProjectionOnto
      (rankQNormalBlock (rankQActualReference F hF x))
      (fun l ↦ rankQPreparationWeights l.1 l.2)
      (show 0 < eps / 4 by positivity)
  obtain ⟨Ucut, hUcutsub, hUcut, hxUcut⟩ := mem_nhds_iff.mp packet.one_near
  obtain ⟨Wcut, hWcutsub, hWcut, hyWcut⟩ := mem_nhds_iff.mp packet.zero_near
  exact ⟨{
    directions := d
    independent := hli
    margin := margin
    margin_pos := hm
    frame_lower := hframe
    tolerance := eps
    tolerance_pos := heps
    coefficient_budget := hbudget
    neighborhood := (U ∩ Ucut) ×ˢ Wcut
    neighborhood_open := (hU.inter hUcut).prod hWcut
    center_mem := ⟨⟨hxU, hxUcut⟩, hyWcut⟩
    support := fun z hz ↦ hUsupport hz.1.1
    cutoff := fun z hz l ↦ ⟨hUcutsub hz.1.2 l, hWcutsub hz.2 l⟩
    principal_variation := fun z hz l ↦ hprincipal z.1 hz.1.1 l
    source_variation := fun z hz ↦ hsource z.1 hz.1.1 }⟩

end GlobalEmbedding.Upgrade
