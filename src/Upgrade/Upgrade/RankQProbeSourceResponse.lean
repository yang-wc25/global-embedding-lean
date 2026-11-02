import Upgrade.IncidencePerturbation
import Upgrade.SupportedProbeJointSmooth
import Upgrade.CompactFixedAtlasJets

/-!
# Actual first-source response from original probe C² control

This common consumer applies to Schur and supported equations. It derives the
value-source error from the original atlas C² norm, retaining the actual
center-to-point first-jet variation. The equation-source derivative is the
full derivative of the identified true form in its actual changing source
frame. Its bound K is displayed and is not inferred from arbitrary smooth Q.
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

/-- The same full probes geometry supplies spatial differentiability of the
literal true-form coordinate field. -/
theorem ProbeGeometry.actual_coordinate_source_differentiable
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source) :
    DifferentiableAt ℝ
      (fun s ↦ actualSupportedProbeCoordinate F₀ (g.map t) (g.slice_smooth t)
        (g.normalIdentification t) A hA i x hx (u,s)) (A.chart i z) := by
  have hu' : u ∈ Metric.ball 0 g.radius := by simpa using hu
  have hw : (u,A.chart i z) ∈ Metric.ball 0 g.radius ×ˢ (A.chart i).target :=
    ⟨hu', (A.chart i).map_source hz⟩
  have hC := ((g.actual_supported_coordinate_smooth A hA i x hx t ht htt).contDiffAt
    ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hw)).differentiableAt (by simp)
  have hpair : DifferentiableAt ℝ (fun s : E ↦ (u,s)) (A.chart i z) :=
    differentiableAt_const u |>.prodMk differentiableAt_id
  exact hC.comp (A.chart i z) hpair

/-- The original C² probe estimate and original first-jet variation supply the
actual source-column value error. Every source derivative of Q and the source
frame remains in the literal composed derivative bounded by K. -/
theorem ExactProbeFamily.actual_source_incidence_error
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (z y : M) (hz : z ∈ A.support i)
    {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (equation : (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) → R)
    (sigma a : ℝ) (ha : a ≠ 0) (K beta : ℝ)
    (hbeta : ‖probeAtlasFirstJet A F₀ i z - probeAtlasFirstJet A F₀ i x‖ ≤ beta) :
    let C := fun v s ↦ actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hx (v,s)
    DifferentiableAt ℝ equation (C u (A.chart i z)) →
    ‖(fderiv ℝ equation (C u (A.chart i z))).comp
        (fderiv ℝ (C u) (A.chart i z))‖ ≤ K →
    ∀ v : E,
      ‖fderiv ℝ
          (fun s ↦ scaledIncidence C
            (fun w q ↦ probe.map t w ((A.chart i).symm q)) (probe.map t)
            equation sigma a u s y) (A.chart i z) (a • v) -
        (0, probeAtlasFirstJet A F₀ i x v)‖ ≤
      max (|a / sigma| * K)
        (probeAtlasDerivativeConstant n N 1 *
          (probe.constant * t ^ ((44 : ℝ) / 5)) + beta) * ‖v‖ := by
  intro C hR hK v
  have hzs := hA.support_subset i hz
  have hB := probe.toProbeGeometry.actual_coordinate_source_differentiable
    A hA i x hx t ht htt u hu z hzs
  have hF := ((probeAtlas_fixed_coordinate_smooth A hA (probe.map t u)
    (probe.slice_smooth t u) i).contDiffAt
      ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hzs))).differentiableAt (by simp)
  have hjet := (probeAtlas_original_two_jet_difference A hA F₀ (probe.map t u) hF₀
    (probe.slice_smooth t u)
    (mul_nonneg probe.constant_nonneg (Real.rpow_nonneg ht.le _))
    (probe.closeness t ht htt u hu) i z hz).1
  have hclose : ‖fderiv ℝ (fun s ↦ probe.map t u ((A.chart i).symm s)) (A.chart i z) -
      probeAtlasFirstJet A F₀ i x‖ ≤
        probeAtlasDerivativeConstant n N 1 * (probe.constant * t ^ ((44 : ℝ) / 5)) + beta := by
    exact (norm_sub_le_norm_sub_add_norm_sub
      (probeAtlasFirstJet A (probe.map t u) i z)
      (probeAtlasFirstJet A F₀ i z) (probeAtlasFirstJet A F₀ i x)).trans
        (add_le_add hjet hbeta)
  exact scaledIncidence_source_error_le
    C (fun w q ↦ probe.map t w ((A.chart i).symm q)) (probe.map t) equation
    sigma a ha u (A.chart i z) y v hB hR hF (probeAtlasFirstJet A F₀ i x)
    K _ hK hclose

#print axioms ProbeGeometry.actual_coordinate_source_differentiable
#print axioms ExactProbeFamily.actual_source_incidence_error
end GlobalEmbedding.Upgrade
