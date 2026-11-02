import Upgrade.SupportedProbeJointSmooth
import Upgrade.RankQProbeResponse
import Upgrade.IncidenceLeadingMargins

/-!
# Native actual supported responses from the full original probe interface

The original parameter response is transported through the same fixed source
normalization and actual old-center projection. The native joint derivative
is identified with this response on the horizontal parameter subspace.
Current leading-field variation is explicitly retained when comparing with
the legal packet at its center. No incidence rank is an input.
-/

noncomputable section
open Bundle Manifold Set Module
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

private theorem supported_scaled_reference_difference
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (current reference : S) (a σ β : ℝ) (hσ : 0 ≤ σ)
    (ha : |a| ≤ σ) (hβ : ‖current - reference‖ ≤ β) :
    ‖a • current - a • reference‖ ≤ σ * β := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul ha hβ (norm_nonneg _) hσ

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Horizontal columns of the literal actual supported incidence are the
same native parameter derivatives as in the original probe estimates. -/
theorem ProbeGeometry.actual_supported_coordinate_joint_parameter
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source) (d : ProbeParameters r) :
    fderiv ℝ (actualSupportedProbeCoordinate F₀ (g.map t) (g.slice_smooth t)
        (g.normalIdentification t) A hA i x hx) (u, A.chart i z) (d, 0) =
      fderiv ℝ (fun v ↦ projectedIdentifiedTrueForm F₀ (g.map t v) (g.slice_smooth t v)
        (g.normalIdentification t v) x z (probeAtlasNormalizedFrame A hA i x hx z)) u d := by
  let C := actualSupportedProbeCoordinate F₀ (g.map t) (g.slice_smooth t)
    (g.normalIdentification t) A hA i x hx
  have hw : (u, A.chart i z) ∈ Metric.ball 0 g.radius ×ˢ (A.chart i).target :=
    ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hu, (A.chart i).map_source hz⟩
  have hC : DifferentiableAt ℝ C (u, A.chart i z) :=
    ((g.actual_supported_coordinate_smooth A hA i x hx t ht htt).contDiffAt
      ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hw)).differentiableAt (by simp)
  have hslice : (fun v ↦ C (v, A.chart i z)) =
      (fun v ↦ projectedIdentifiedTrueForm F₀ (g.map t v) (g.slice_smooth t v)
        (g.normalIdentification t v) x z (probeAtlasNormalizedFrame A hA i x hx z)) := by
    funext v
    change projectedIdentifiedTrueForm F₀ (g.map t v) (g.slice_smooth t v)
      (g.normalIdentification t v) x ((A.chart i).symm (A.chart i z))
        (probeAtlasNormalizedFrame A hA i x hx ((A.chart i).symm (A.chart i z))) = _
    rw [(A.chart i).left_inv hz]
  have hd := actual_parameter_fderiv_eq_joint C hC
  rw [hslice] at hd
  exact (congrArg (fun L ↦ L d) hd).symm

/-- The original true-form probe response, now as a column of the actual
joint supported incidence. The entire original remainder and the fixed
inverse-frame norm multiplier remain in the estimate. -/
theorem ExactProbeFamily.actual_supported_coordinate_response
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (l : Fin r) (b : Bool) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (z : M) (hz : z ∈ A.support i) :
    ‖fderiv ℝ (actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hx) (u, A.chart i z) (Pi.single (l, b) 1, 0) -
      (t ^ ((44 : ℝ) / 5) * probeTrig b (probe.weight l * (waves l).phase z /
        t ^ ((6 : ℝ) / 5))) •
        (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
          (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx z) ((waves l).tensor z))‖ ≤
      t ^ ((44 : ℝ) / 5) *
        ((probe.etaB t + probe.constant * ‖u‖) * ‖probeAtlasNormalizationSquare A hA i x hx‖) := by
  rw [probe.toProbeGeometry.actual_supported_coordinate_joint_parameter A hA i x hx t ht htt
    u hu z (hA.support_subset i hz) (Pi.single (l, b) 1)]
  exact probe.projected_normalized_secondForm_response hA t ht htt u hu l b i x hx z hz

private theorem supported_probeTrig_abs_le_one (b : Bool) (θ : ℝ) :
    |probeTrig b θ| ≤ 1 := by
  cases b
  · exact Real.abs_cos_le_one θ
  · exact Real.abs_sin_le_one θ

/-- Comparison with an actual reference packet retains the spatial
variation β of its literal normalized leading tensor. This β is unweighted
and can be fixed before the probe provider returns its frequencies. -/
theorem ExactProbeFamily.actual_supported_coordinate_response_reference
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (l : Fin r) (b : Bool) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (z : M) (hz : z ∈ A.support i)
    (T : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) (β : ℝ)
    (hβ : ‖(normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
      (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx z) ((waves l).tensor z)) - T‖ ≤ β) :
    ‖fderiv ℝ (actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hx) (u, A.chart i z) (Pi.single (l, b) 1, 0) -
      (t ^ ((44 : ℝ) / 5) * probeTrig b (probe.weight l * (waves l).phase z /
        t ^ ((6 : ℝ) / 5))) • T‖ ≤
      t ^ ((44 : ℝ) / 5) *
        ((probe.etaB t + probe.constant * ‖u‖) * ‖probeAtlasNormalizationSquare A hA i x hx‖ + β) := by
  let σ := t ^ ((44 : ℝ) / 5)
  let θ := probe.weight l * (waves l).phase z / t ^ ((6 : ℝ) / 5)
  let current := (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
    (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx z) ((waves l).tensor z))
  have hσ : 0 ≤ σ := Real.rpow_nonneg ht.le _
  have htrig : |σ * probeTrig b θ| ≤ σ := by
    rw [abs_mul, abs_of_nonneg hσ]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (supported_probeTrig_abs_le_one b θ) hσ
  have hvariation : ‖(σ * probeTrig b θ) • current - (σ * probeTrig b θ) • T‖ ≤ σ * β := by
    exact supported_scaled_reference_difference current T _ σ β hσ htrig hβ
  have hraw := probe.actual_supported_coordinate_response hA t ht htt u hu l b i x hx z hz
  have hbound := incidence_error_add_reference_variation
    (S := SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) _ _ _ _ _ hraw hvariation
  exact hbound.trans_eq (mul_add σ _ β).symm

#print axioms ProbeGeometry.actual_supported_coordinate_joint_parameter
#print axioms ExactProbeFamily.actual_supported_coordinate_response
#print axioms ExactProbeFamily.actual_supported_coordinate_response_reference

end GlobalEmbedding.Upgrade
