import Upgrade.SupportedProbeAvoidance

/-!
# Actual probe values in the accepted finite parameter coordinates

The original sine/cosine array is transported by one fixed continuous linear
equivalence. The family is literally the same map with that parameter change.
This supplies the native derivatives and joint smoothness needed by the
already accepted paired-value and avoidance consumers.
-/

noncomputable section
open Bundle Manifold Set Module Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The same actual probe family in fixed finite parameter coordinates. -/
def ProbeGeometry.coordinateMap {F₀ : M → V} {r : ℕ}
    (g : ProbeGeometry (n := n) F₀ r) (t : ℝ)
    (v : Fin (finrank ℝ (ProbeParameters r)) → ℝ) (z : M) : V :=
  g.map t ((probeParameterCoordinates r).symm v) z

def ProbeGeometry.coordinateDomain {F₀ : M → V} {r : ℕ}
    (g : ProbeGeometry (n := n) F₀ r) :
    Set (Fin (finrank ℝ (ProbeParameters r)) → ℝ) :=
  (probeParameterCoordinates r).symm ⁻¹' Metric.ball 0 g.radius

theorem ProbeGeometry.coordinateDomain_open {F₀ : M → V} {r : ℕ}
    (g : ProbeGeometry (n := n) F₀ r) : IsOpen g.coordinateDomain :=
  Metric.isOpen_ball.preimage (probeParameterCoordinates r).symm.continuous

/-- Native parameter differentiability at every actual source point follows
directly from joint smoothness; no atlas membership is an extra premise. -/
theorem ProbeGeometry.value_parameter_differentiable {F₀ : M → V} {r : ℕ}
    (g : ProbeGeometry (n := n) F₀ r)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < g.radius) (z : M) :
    DifferentiableAt ℝ (fun v ↦ g.map t v z) u := by
  have hmem : (u,z) ∈ Metric.ball 0 g.radius ×ˢ (univ : Set M) :=
    ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hu, mem_univ _⟩
  exact (((g.joint_smooth t ht htt).contMDiffAt
    ((Metric.isOpen_ball.prod isOpen_univ).mem_nhds hmem)).curry_left
    ).contDiffAt.differentiableAt (by simp)

/-- Joint smoothness of the exact same actual family under fixed parameter
coordinates. The original parameter ball becomes its honest preimage. -/
theorem ProbeGeometry.coordinateMap_joint_smooth {F₀ : M → V} {r : ℕ}
    (g : ProbeGeometry (n := n) F₀ r)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold) :
    ContMDiffOn ((𝓘(ℝ, Fin (finrank ℝ (ProbeParameters r)) → ℝ)).prod IM)
      𝓘(ℝ, V) ∞ (Function.uncurry (g.coordinateMap t))
        (g.coordinateDomain ×ˢ univ) := by
  let α := probeParameterCoordinates r
  have hchange : ContMDiff ((𝓘(ℝ, Fin (finrank ℝ (ProbeParameters r)) → ℝ)).prod IM)
      ((𝓘(ℝ, ProbeParameters r)).prod IM) ∞
      (fun z : (Fin (finrank ℝ (ProbeParameters r)) → ℝ) × M ↦ (α.symm z.1, z.2)) :=
    (α.symm.contDiff.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  exact (g.joint_smooth t ht htt).comp hchange.contMDiffOn
    (fun z hz ↦ ⟨hz.1, mem_univ _⟩)

/-- Native derivative identity on transported actual parameter directions.
This differentiates the fixed parameter equivalence, never fast-angle
coefficients later used to prove rank. -/
theorem ProbeGeometry.coordinateMap_parameter_response {F₀ : M → V} {r : ℕ}
    (g : ProbeGeometry (n := n) F₀ r)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < g.radius) (z : M) :
    fderiv ℝ (fun v ↦ g.coordinateMap t v z) (probeParameterCoordinates r u)
      (probeParameterCoordinates r d) = fderiv ℝ (fun v ↦ g.map t v z) u d := by
  let α := probeParameterCoordinates r
  have hD := g.value_parameter_differentiable t ht htt u hu z
  have hD' : HasFDerivAt (fun v ↦ g.map t v z)
      (fderiv ℝ (fun v ↦ g.map t v z) u) (α.symm (α u)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hD.hasFDerivAt
  have hcomp := hD'.comp (α u) α.symm.hasFDerivAt
  simpa only [ProbeGeometry.coordinateMap, Function.comp_def, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using
    congrArg (fun L ↦ L (α d)) hcomp.fderiv

#print axioms ProbeGeometry.value_parameter_differentiable
#print axioms ProbeGeometry.coordinateMap_joint_smooth
#print axioms ProbeGeometry.coordinateMap_parameter_response

end GlobalEmbedding.Upgrade
