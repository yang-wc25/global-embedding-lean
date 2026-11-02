import Round2.GaugeActualBound
import Upgrade.RankQResidualNorms

/-!
# No-DQ bounds at the actual Schur and supported incidence zeros

These applications discharge orbit annihilation from the proved geometry of
the SAME local defining equations. Neither a differential-rank hypothesis nor
a quantitative derivative bound for the chosen identification is supplied.
-/

noncomputable section
open Function Filter Manifold Module Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

private noncomputable local instance gaugeZeroFormNorm (F₀ : M → V) (x : M) :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance gaugeZeroFormSpace (F₀ : M → V) (x : M) :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance gaugeZeroResidualNorm (F₀ : M → V) (x : M)
    (B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :
    NormedAddCommGroup (B.ker →L[ℝ] B.rangeᗮ) := rankQResidualNormedAddCommGroup B
private noncomputable local instance gaugeZeroResidualSpace (F₀ : M → V) (x : M)
    (B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :
    NormedSpace ℝ (B.ker →L[ℝ] B.rangeᗮ) := rankQResidualNormedSpace B

/-- The literal Schur source derivative has a fixed C³ bound at every actual
Schur incidence zero, with the original fixed reference block unchanged. -/
theorem ExactProbeFamily.actual_rankQ_source_derivative_bound_at_zero
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    (himm₀ : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (z : M) (hz : z ∈ A.support i)
    (hgap : ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    (B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)
    (Kbound : ℝ) (hK : ‖probeAtlasTangentLeftInverse A (probe.map t u) i z‖ ≤ Kbound) :
    let C := actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hx (u, A.chart i z)
    (rankQBlockA B C).IsInvertible → rankQSchur B C = 0 →
    ‖(fderiv ℝ (rankQSchur B) C).comp (fderiv ℝ
      (fun s ↦ actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hx (u, s)) (A.chart i z))‖ ≤
      ‖fderiv ℝ (rankQSchur B) C‖ * probe.gaugeSpatialBound hA i x hx Kbound := by
  intro C hblock hzero
  exact probe.actual_incidence_source_derivative_without_gauge_bound himm₀ hA i x hx
    t ht htt u hu z hz hgap (fderiv ℝ (rankQSchur B) C)
    (rankQSchur_fderiv_target_orbit_zero B C hblock hzero) Kbound hK

/-- The SAME accepted supported defining equation has a fixed C³ source
bound at every actual supported zero. This permits the dimension-three joint
incidence argument without pretending that all supported kernels disappear. -/
theorem ExactProbeFamily.actual_supported_source_derivative_bound_at_zero
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    (himm₀ : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (z : M) (hz : z ∈ A.support i)
    (hgap : ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    {ambient : Set (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)}
    {B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x}
    (chart : SupportedLocusLocalEquations ambient
      {D : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x |
        HasSupportedKernel D.toLinearMap} B)
    (Kbound : ℝ) (hK : ‖probeAtlasTangentLeftInverse A (probe.map t u) i z‖ ≤ Kbound) :
    let C := actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hx (u, A.chart i z)
    C ∈ chart.domain → chart.equation C = 0 →
    ‖(fderiv ℝ chart.equation C).comp (fderiv ℝ
      (fun s ↦ actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hx (u, s)) (A.chart i z))‖ ≤
      ‖fderiv ℝ chart.equation C‖ * probe.gaugeSpatialBound hA i x hx Kbound := by
  intro C hdom hzero
  exact probe.actual_incidence_source_derivative_without_gauge_bound himm₀ hA i x hx
    t ht htt u hu z hz hgap (fderiv ℝ chart.equation C)
    (supportedEquation_fderiv_target_orbit_zero chart hdom hzero) Kbound hK

#print axioms ExactProbeFamily.actual_rankQ_source_derivative_bound_at_zero
#print axioms ExactProbeFamily.actual_supported_source_derivative_bound_at_zero

end GlobalEmbedding.Upgrade
