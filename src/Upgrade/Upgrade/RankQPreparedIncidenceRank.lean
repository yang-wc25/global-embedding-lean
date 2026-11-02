import Upgrade.CompactRankQPreparation
import Upgrade.RankQActualRegularity
import Upgrade.IncidenceFiniteColumns

/-!
# The prepared actual rank-q frame forces the actual incidence rank

All principal columns and their finite margin were constructed from the actual
local legal packet with preparation weights 1 and 2 before probes and before
the finite cover. The source preimages use the inverse of the actual center
atlas frame. This specializes the accepted finite-column stability consumer
to the literal new-map Schur incidence; its rank is never a hypothesis.
-/

noncomputable section
open Function Manifold Module Set
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

attribute [local instance] actualResidualNormedAddCommGroup actualResidualNormedSpace
  actualResidualFiniteDimensional actualJointNorm

/-- The prepared native source vectors are converted through the actual
inverse atlas frame; no identity source-frame assumption is made. -/
theorem RankQPreparedNeighborhood.actual_atlas_frame_identity
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQPreparedNeighborhood A hA p i hx) (j : Fin (2 * n + 1)) :
    (∑ l : Fin n × Fin 2, (prep.directions j).1 l •
      rankQActualPrincipalColumn F₀ hF₀ x ((p.waves l.1).tensor x)
        (-((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (p.waves l.1).value x)) +
      (0, probeAtlasFirstJet A F₀ i x
        ((probeAtlasInverseFrameEquiv A hA i x
          (hA.support_subset i (interior_subset hx))).symm (prep.directions j).2)) =
      p.principalMap rankQPreparationWeights (prep.directions j) := by
  have hsource :
      (0, probeAtlasFirstJet A F₀ i x
        ((probeAtlasInverseFrameEquiv A hA i x
          (hA.support_subset i (interior_subset hx))).symm (prep.directions j).2)) =
        rankQActualTangentColumn F₀ hF₀ x (prep.directions j).2 := by
    apply Prod.ext
    · rfl
    · exact probeAtlasFirstJet_inverse_center A hA F₀ hF₀ i x
        (hA.support_subset i (interior_subset hx)) (prep.directions j).2
  rw [hsource]
  exact (rankQActualJointPrincipalMap_apply (I := IM) F₀ hF₀ x
    (fun l : Fin n × Fin 2 ↦ (p.waves l.1).tensor x)
    (fun l : Fin n × Fin 2 ↦ -((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) •
      (p.waves l.1).value x) (prep.directions j)).symm

/-- The literal actual derivative has rank at least 2n+1 once its two measured
partial-response errors fit the pre-probe geometric margin. This theorem
keeps the parameter type AFTER the prepared margin, so it is independent of
the final global finite wave count. -/
theorem RankQPreparedNeighborhood.actual_joint_rank_of_response
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQPreparedNeighborhood A hA p i hx)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (G : P → M → V) (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (j : Fin A.count) (sigma a : ℝ) (w : P × (E × E)) :
    let hxc := hA.support_subset i (interior_subset hx)
    let J := actualRankQJointIncidence F₀ hF₀ G hG Q A hA i j x hxc sigma a
    DifferentiableAt ℝ J w →
    ∀ dirs : (Fin n × Fin 2) → P,
    (∀ l, ‖fderiv ℝ (fun v ↦ J (v,w.2)) w.1 (dirs l) -
      rankQActualPrincipalColumn F₀ hF₀ x ((p.waves l.1).tensor x)
        (-((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (p.waves l.1).value x)‖ ≤
        prep.tolerance) →
    (∀ v, ‖fderiv ℝ (fun s ↦ J (w.1,s,w.2.2)) w.2.1 (a • v) -
      (0, probeAtlasFirstJet A F₀ i x v)‖ ≤ prep.tolerance * ‖v‖) →
    2 * n + 1 ≤ finrank ℝ (fderiv ℝ J w).range := by
  intro hxc J hJ dirs hp hs
  let principal := fun l : Fin n × Fin 2 ↦
    rankQActualPrincipalColumn F₀ hF₀ x ((p.waves l.1).tensor x)
      (-((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (p.waves l.1).value x)
  let c := fun k : Fin (2 * n + 1) ↦ (prep.directions k).1
  let e := fun k : Fin (2 * n + 1) ↦
    (probeAtlasInverseFrameEquiv A hA i x hxc).symm (prep.directions k).2
  let b := prep.margin / (2 * ((2 * n + 1 : ℕ) + 1 : ℝ))
  have hb : 0 < b := div_pos prep.margin_pos (by positivity)
  have hframe : ∀ z : Fin (2 * n + 1) → ℝ,
      prep.margin * ‖z‖ ≤ ‖∑ k, z k •
        ((∑ l, c k l • principal l) + (0, probeAtlasFirstJet A F₀ i x (e k)))‖ := by
    intro z
    have heq (k : Fin (2 * n + 1)) :
        (∑ l, c k l • principal l) + (0, probeAtlasFirstJet A F₀ i x (e k)) =
          p.principalMap rankQPreparationWeights (prep.directions k) :=
      prep.actual_atlas_frame_identity k
    simpa only [heq] using! prep.frame_lower z
  have hsmall : ((2 * n + 1 : ℕ) : ℝ) * b < prep.margin := by
    dsimp only [b]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * ((2 * n + 1 : ℕ) + 1 : ℝ))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (2 * n + 1), prep.margin_pos]
  have hr := jointScaledIncidence_rank_of_finite_principal_frame
    (ι := Fin n × Fin 2) (k := 2 * n + 1) (P := P) (X := E) (Y := E)
    (T := SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)
    (R := (rankQActualReference F₀ hF₀ x).ker →L[ℝ] (rankQActualReference F₀ hF₀ x).rangeᗮ)
    («V» := V)
    (fun u s ↦ actualSupportedProbeCoordinate F₀ G hG Q A hA i x hxc (u,s))
    (fun u s ↦ G u ((A.chart i).symm s))
    (fun u s ↦ G u ((A.chart j).symm s))
    (rankQSchur (rankQActualReference F₀ hF₀ x)) sigma a w.1 w.2.1 w.2.2
    hJ dirs principal (probeAtlasFirstJet A F₀ i x) c e prep.margin
    prep.tolerance prep.tolerance b prep.tolerance_pos.le hb.le hframe hp hs
    prep.coefficient_budget hsmall
  exact hr

#print axioms RankQPreparedNeighborhood.actual_atlas_frame_identity
#print axioms RankQPreparedNeighborhood.actual_joint_rank_of_response
end GlobalEmbedding.Upgrade
