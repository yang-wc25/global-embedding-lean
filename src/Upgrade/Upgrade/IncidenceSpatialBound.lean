import Upgrade.IncidenceNormalControl
import Upgrade.SupportedProbeC3
import Upgrade.RankQProbeSourceResponse

/-!
# The actual C³ source bound under the selected normal-identification control

This wraps the genuine spatial Hessian calculation. The derivative of the
same actual ambient normal-identification operator includes its changing
normal projector; the fixed atlas Hessian identity includes the changing
source frame. The original probe C³ bound supplies derivatives of orders two
and three. No unspecified bounded derivative of an arbitrary form remains.
-/

noncomputable section
open Function Manifold Module Set
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

private noncomputable local instance incidenceSpatialFormNormed (F₀ : M → V) (x : M) :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance incidenceSpatialFormSpace (F₀ : M → V) (x : M) :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedSpace

/-- The explicit fixed source-derivative constant for one prepared chart. -/
def ChosenProbeNormalControl.coordinateSpatialBound
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    {probe : ExactProbeFamily F₀ hF₀ A waves} (control : ChosenProbeNormalControl probe)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source) : ℝ :=
  (control.spatialBound *
      (actualHessianLiftConstant E V * (probeAtlasDerivativeConstant n N 2 * probe.constant)) +
    actualHessianLiftConstant E V * (probeAtlasDerivativeConstant n N 3 * probe.constant)) *
      ‖probeAtlasNormalizationSquare A hA i x hx‖

theorem ChosenProbeNormalControl.coordinateSpatialBound_nonneg
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    {probe : ExactProbeFamily F₀ hF₀ A waves} (control : ChosenProbeNormalControl probe)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source) :
    0 ≤ control.coordinateSpatialBound hA i x hx := by
  unfold coordinateSpatialBound
  have hL := control.spatialBound_nonneg
  have hC := probe.constant_nonneg
  have hH := actualHessianLiftConstant_nonneg («E» := E) (F := V)
  have h₂ := probeAtlasDerivativeConstant_nonneg n N 2
  have h₃ := probeAtlasDerivativeConstant_nonneg n N 3
  positivity

/-- Uniform bound for the literal source derivative of the actual incidence
form, obtained solely from the full probes C³ estimate and the selected Q
control. The same fixed chart and source normalization occur throughout. -/
theorem ChosenProbeNormalControl.actual_coordinate_spatial_bound
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    {probe : ExactProbeFamily F₀ hF₀ A waves} (control : ChosenProbeNormalControl probe)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (z : M) (hz : z ∈ A.support i) :
    ‖fderiv ℝ
      (fun s ↦ actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hx (u, s)) (A.chart i z)‖ ≤
      control.coordinateSpatialBound hA i x hx := by
  have h := probe.actual_supported_coordinate_spatial_derivative_bound
    hA i x hx t ht htt u hu z hz control.spatialBound
    (control.spatial_derivative_bound t ht htt u hu i z hz)
  exact h

/-- The scale factor in the actual source column is exactly the original
positive power from the paper, so a fixed bound tends to zero with t. -/
theorem actual_probe_source_scale_ratio (t : ℝ) (ht : 0 < t) :
    |t ^ ((56 : ℝ) / 5) / t ^ ((44 : ℝ) / 5)| = t ^ ((12 : ℝ) / 5) := by
  rw [← Real.rpow_sub ht]
  norm_num only [show (56 : ℝ) / 5 - 44 / 5 = 12 / 5 by norm_num]
  exact abs_of_pos (Real.rpow_pos_of_pos ht _)

#print axioms ChosenProbeNormalControl.actual_coordinate_spatial_bound
#print axioms actual_probe_source_scale_ratio

end GlobalEmbedding.Upgrade
