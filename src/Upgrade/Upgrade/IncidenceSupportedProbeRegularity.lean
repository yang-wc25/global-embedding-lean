import Upgrade.IncidenceSupportedProbeData
import Upgrade.RankQActualIncidence

/-! Actual joint differentiability of the two-chart supported incidence,
derived from the same full probes geometry and the actual equation domain. -/

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

theorem SupportedJointWavePacket.probeData_differentiable
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    (p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y₀)
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (hx : x ∈ (A.chart i).source)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius) (j : Fin A.count)
    (xi eta : E) (hxi : xi ∈ (A.chart i).target) (heta : eta ∈ (A.chart j).target)
    (hdom : actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hx (u,xi) ∈ p.chart.domain) :
    DifferentiableAt ℝ (p.probeData hA i hx probe t j).incidence (u,xi,eta) := by
  have hu' : u ∈ Metric.ball 0 probe.radius := by simpa using hu
  have hxU : (u,xi) ∈ Metric.ball 0 probe.radius ×ˢ (A.chart i).target := ⟨hu',hxi⟩
  have hyU : (u,eta) ∈ Metric.ball 0 probe.radius ×ˢ (A.chart j).target := ⟨hu',heta⟩
  have hBx := (probe.toProbeGeometry.actual_supported_coordinate_smooth A hA i x hx t ht htt).contDiffAt
    ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hxU)
  have hFx := (contDiffOn_actual_parameter_atlas_pullback A hA i
    (Function.uncurry (probe.map t)) (probe.joint_smooth t ht htt)).contDiffAt
      ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hxU)
  have hHy := (contDiffOn_actual_parameter_atlas_pullback A hA j
    (Function.uncurry (probe.map t)) (probe.joint_smooth t ht htt)).contDiffAt
      ((Metric.isOpen_ball.prod (A.chart j).open_target).mem_nhds hyU)
  have hR := p.chart.contDiffOn_equation.contDiffAt (p.chart.isOpen_domain.mem_nhds hdom)
  have h := rankQ_jointScaledIncidence_differentiableAt
    (P := ProbeParameters r) (X := E) (Y := E)
    (T := SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)
    (R := Fin p.chart.codim → ℝ) («V» := V)
    (fun v z ↦ actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hx (v,z))
    (fun v z ↦ probe.map t v ((A.chart i).symm z))
    (fun v z ↦ probe.map t v ((A.chart j).symm z))
    p.chart.equation (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5)) u xi eta
    (hBx.differentiableAt (by simp)) (hFx.differentiableAt (by simp))
    (hHy.differentiableAt (by simp)) (hR.differentiableAt (by simp))
  exact h

#print axioms SupportedJointWavePacket.probeData_differentiable
end GlobalEmbedding.Upgrade
