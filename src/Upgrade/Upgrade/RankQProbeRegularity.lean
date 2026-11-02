import Upgrade.RankQActualRegularity

/-!
# Actual probe geometry supplies the differentiable rank-q incidence

This endpoint consumes only the full probe geometry and the protected actual
Schur block. Both distinct atlas charts and the actual source-frame variation
remain inside the differentiated map.
-/

noncomputable section
open Function Manifold Module Set
open scoped ContDiff Topology
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

attribute [local instance] residualNormedAddCommGroup residualNormedSpace

/-- The same actual probe family makes its literal Schur/value incidence
jointly differentiable at every admitted parameter and protected chart point. -/
theorem ProbeGeometry.actual_rankQ_incidence_differentiable
    {F₀ : M → V} (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i j : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (xi eta : E) (hxi : xi ∈ (A.chart i).target) (heta : eta ∈ (A.chart j).target)
    (sigma a : ℝ)
    (hblock : (rankQBlockA (rankQActualReference F₀ hF₀ x)
      (actualSupportedProbeCoordinate F₀ (g.map t) (g.slice_smooth t)
        (g.normalIdentification t) A hA i x hx (u,xi))).IsInvertible) :
    DifferentiableAt ℝ
      (actualRankQJointIncidence F₀ hF₀ (g.map t) (g.slice_smooth t)
        (g.normalIdentification t) A hA i j x hx sigma a) (u,xi,eta) := by
  have hu' : u ∈ Metric.ball 0 g.radius := by
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hxU : (u,xi) ∈ Metric.ball 0 g.radius ×ˢ (A.chart i).target := ⟨hu',hxi⟩
  have hyU : (u,eta) ∈ Metric.ball 0 g.radius ×ˢ (A.chart j).target := ⟨hu',heta⟩
  have hBx := (g.actual_supported_coordinate_smooth A hA i x hx t ht htt).contDiffAt
    ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hxU)
  have hFx := (contDiffOn_actual_parameter_atlas_pullback A hA i
    (Function.uncurry (g.map t)) (g.joint_smooth t ht htt)).contDiffAt
      ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hxU)
  have hHy := (contDiffOn_actual_parameter_atlas_pullback A hA j
    (Function.uncurry (g.map t)) (g.joint_smooth t ht htt)).contDiffAt
      ((Metric.isOpen_ball.prod (A.chart j).open_target).mem_nhds hyU)
  have hR := rankQSchur_contDiffAt (rankQActualReference F₀ hF₀ x)
    (actualSupportedProbeCoordinate F₀ (g.map t) (g.slice_smooth t)
      (g.normalIdentification t) A hA i x hx (u,xi)) hblock
  have h := rankQ_jointScaledIncidence_differentiableAt
    (P := ProbeParameters r) (X := E) (Y := E)
    (T := SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)
    (R := (rankQActualReference F₀ hF₀ x).ker →L[ℝ] (rankQActualReference F₀ hF₀ x).rangeᗮ)
    («V» := V)
    (fun v z ↦ actualSupportedProbeCoordinate F₀ (g.map t) (g.slice_smooth t)
      (g.normalIdentification t) A hA i x hx (v,z))
    (fun v z ↦ g.map t v ((A.chart i).symm z))
    (fun v z ↦ g.map t v ((A.chart j).symm z))
    (rankQSchur (rankQActualReference F₀ hF₀ x)) sigma a u xi eta
    (hBx.differentiableAt (by simp)) (hFx.differentiableAt (by simp))
    (hHy.differentiableAt (by simp)) (hR.differentiableAt (by simp))
  exact h

#print axioms ProbeGeometry.actual_rankQ_incidence_differentiable
end GlobalEmbedding.Upgrade
