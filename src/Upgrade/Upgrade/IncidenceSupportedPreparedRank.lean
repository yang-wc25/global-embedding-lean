import Upgrade.CompactSupportedJointPreparation
import Upgrade.IncidenceSupportedGeometry

/-!
# Actual joint rank from the already fixed supported preparation

The frame, source preimages, tolerance and coefficient budget were constructed
before the global wave list and returned weights. This theorem applies that
same frame to the native full derivative of the literal new-map incidence.
Neither its rank nor a freshly selected reference frame is an assumption.
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

theorem SupportedJointPreparedNeighborhood.actual_joint_rank_of_response
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    {p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : SupportedJointPreparedNeighborhood A hA p i hx)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (data : p.IncidenceData A hA i (hA.support_subset i (interior_subset hx)) P)
    (w : P × (E × E)) (hJ : DifferentiableAt ℝ data.incidence w)
    (dirs : (Fin (n * (n - 1) / 2 + n) × Fin 2) → P)
    (hp : ∀ l, ‖fderiv ℝ (fun u ↦ data.incidence (u, w.2)) w.1 (dirs l) -
      supportedJointPrincipalColumn (incidenceActualTangent (n := n) F₀ x)
        p.equationColumns p.valueNormals rankQPreparationWeights l‖ ≤ prep.tolerance)
    (hs : ∀ v, ‖fderiv ℝ (fun s ↦ data.incidence (w.1, s, w.2.2)) w.2.1 (data.a • v) -
      (0, p.sourceReferenceDerivative A hA i (hA.support_subset i (interior_subset hx)) v)‖ ≤
        prep.tolerance * ‖v‖) :
    n * (n - 1) / 2 + 2 * n ≤ finrank ℝ (fderiv ℝ data.incidence w).range := by
  let k := n * (n - 1) / 2 + 2 * n
  let b := prep.margin / (2 * ((k : ℝ) + 1))
  have hb : 0 < b := div_pos prep.margin_pos (by positivity)
  have hsmall : (k : ℝ) * b < prep.margin := by
    dsimp only [b]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * ((k : ℝ) + 1))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k, prep.margin_pos]
  have h := jointScaledIncidence_rank_of_finite_principal_frame
    (ι := Fin (n * (n - 1) / 2 + n) × Fin 2) (k := k)
    (P := P) (X := E) (Y := E)
    (T := SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)
    (R := Fin p.chart.codim → ℝ) («V» := V)
    (fun u s ↦ actualSupportedProbeCoordinate F₀ data.map data.smooth data.identification
      A hA i x (hA.support_subset i (interior_subset hx)) (u, s))
    (fun u s ↦ data.map u ((A.chart i).symm s))
    (fun u s ↦ data.map u ((A.chart data.secondChart).symm s))
    p.chart.equation data.sigma data.a w.1 w.2.1 w.2.2 hJ dirs
    (supportedJointPrincipalColumn (incidenceActualTangent (n := n) F₀ x)
      p.equationColumns p.valueNormals rankQPreparationWeights)
    (p.sourceReferenceDerivative A hA i (hA.support_subset i (interior_subset hx)))
    prep.coefficients prep.sourceDirections prep.margin prep.tolerance prep.tolerance b
    prep.tolerance_pos.le hb.le prep.frame_lower hp hs prep.coefficient_budget hsmall
  exact h

#print axioms SupportedJointPreparedNeighborhood.actual_joint_rank_of_response

end GlobalEmbedding.Upgrade
