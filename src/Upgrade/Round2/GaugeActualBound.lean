import Round2.GaugeHessian
import Round2.GaugeActualSplitting
import Round2.MetricLeftInverseCompact
import Upgrade.RankQProbeSourceResponse

/-!
# Source derivative bound for the SAME actual probe incidence at its zeros

The original spatial C³ bound supplies the native second and third jets.
Exact metric preservation supplies the actual tangent left-inverse bound.
The selected normal identification is only differentiated to use the exact
identity `T·df=0`; no quantitative estimate for its derivative is required.
The original actual source frame and its fixed center normalization remain.
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

private noncomputable local instance gaugeActualFormNorm (F₀ : M → V) (x : M) :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance gaugeActualFormSpace (F₀ : M → V) (x : M) :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedSpace

/-- A fixed zero-locus spatial bound. The retained quadratic second-jet term
is the moving-tangent correction, and cannot be dropped. -/
def ExactProbeFamily.gaugeSpatialBound
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source) (Kbound : ℝ) : ℝ :=
  (actualHessianLiftConstant E V * (probeAtlasDerivativeConstant n N 3 * probe.constant) +
    (probeAtlasDerivativeConstant n N 2 * probe.constant) * Kbound *
      (actualHessianLiftConstant E V * (probeAtlasDerivativeConstant n N 2 * probe.constant))) *
    ‖probeAtlasNormalizationSquare A hA i x hx‖

theorem ExactProbeFamily.gaugeSpatialBound_nonneg
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    {Kbound : ℝ} (hK : 0 ≤ Kbound) :
    0 ≤ probe.gaugeSpatialBound hA i x hx Kbound := by
  unfold gaugeSpatialBound
  have hC := probe.constant_nonneg
  have hH := actualHessianLiftConstant_nonneg («E» := E) (F := V)
  have h₂ := probeAtlasDerivativeConstant_nonneg n N 2
  have h₃ := probeAtlasDerivativeConstant_nonneg n N 3
  positivity

/-- Actual source-composition bound. The orbit hypothesis is discharged by
`rankQSchur_fderiv_target_orbit_zero` or the SAME supported defining equation;
it is not a new probe output. -/
theorem ExactProbeFamily.actual_incidence_source_derivative_without_gauge_bound
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
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (D : (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) →L[ℝ] Y)
    (hD : ∀ L : normalSpace (I := IM) F₀ x →L[ℝ] normalSpace (I := IM) F₀ x,
      D (L.comp (actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hx (u, A.chart i z))) = 0)
    (Kbound : ℝ) (hK : ‖probeAtlasTangentLeftInverse A (probe.map t u) i z‖ ≤ Kbound) :
    ‖D.comp (fderiv ℝ
      (fun s ↦ actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hx (u, s)) (A.chart i z))‖ ≤
      ‖D‖ * probe.gaugeSpatialBound hA i x hx Kbound := by
  let f := probe.map t u ∘ (A.chart i).symm
  let T := fun s : E ↦ gaugeActualNormalOperator F₀ (probe.map t u)
    (probe.normalIdentification t u) x ((A.chart i).symm s)
  let Ks := probeAtlasNormalizationSquare A hA i x hx
  let K := probeAtlasTangentLeftInverse A (probe.map t u) i z
  let R := gaugeActualNormalRightInverse F₀ (probe.map t u) himm₀
    (probe.normalIdentification t u) x z hgap
  have hzS := hA.support_subset i hz
  have hzT := (A.chart i).map_source hzS
  have hf : ContDiffAt ℝ ∞ f (A.chart i z) :=
    (probeAtlas_fixed_coordinate_smooth A hA (probe.map t u) (probe.slice_smooth t u) i).contDiffAt
      ((A.chart i).open_target.mem_nhds hzT)
  have hQ := probe.toProbeGeometry.normalIdentification_atlas_spatial_differentiable
    A hA i t ht htt u hu z hzS
  have hT : DifferentiableAt ℝ T (A.chart i z) :=
    (differentiableAt_const (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto).clm_comp hQ
  have hTnorm : ‖T (A.chart i z)‖ ≤ 1 := by
    dsimp only [T]
    rw [(A.chart i).left_inv hzS]
    exact gaugeActualNormalOperator_norm_le_one _ _ _ _ _
  have hTL : ∀ᶠ s in 𝓝 (A.chart i z), (T s).comp (fderiv ℝ f s) = 0 := by
    filter_upwards [(A.chart i).open_target.mem_nhds hzT] with s hs
    have h := gaugeActualNormalOperator_comp_firstJet_zero A hA F₀ (probe.map t u)
      (probe.slice_smooth t u) (probe.normalIdentification t u) i x ((A.chart i).symm s)
      ((A.chart i).map_target hs)
    simpa only [probeAtlasFirstJet, (A.chart i).right_inv hs] using! h
  have himm : ∀ q, Function.Injective (mfderiv IM 𝓘(ℝ, V) (probe.map t u) q) :=
    fun q ↦ immersion_of_inducedMetric_eq F₀ (probe.map t u) q
      (probe.metric t ht htt u hu q) (himm₀ q)
  have hsplit : R.comp (T (A.chart i z)) + (fderiv ℝ f (A.chart i z)).comp K =
      ContinuousLinearMap.id ℝ V := by
    have h := gaugeActualNormal_tangent_split A hA F₀ (probe.map t u) (probe.slice_smooth t u)
      himm₀ himm (probe.normalIdentification t u) i x z hzS hgap
    simpa only [T, (A.chart i).left_inv hzS] using! h
  have hsame : (fun s ↦ actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hx (u, s)) =ᶠ[𝓝 (A.chart i z)]
      (fun s ↦ (T s).comp (gaugeNormalizedHessian f Ks s)) := by
    filter_upwards [(A.chart i).open_target.mem_nhds hzT] with s hs
    rw [actualSupportedProbeCoordinate_eq_identified_hessian F₀ (probe.map t)
      (probe.slice_smooth t) (probe.normalIdentification t) A hA i x hx (u, s) hs]
    rfl
  have hbase : actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hx (u, A.chart i z) =
      (T (A.chart i z)).comp (gaugeNormalizedHessian f Ks (A.chart i z)) :=
    hsame.eq_of_nhds
  have hD' : ∀ L : normalSpace (I := IM) F₀ x →L[ℝ] normalSpace (I := IM) F₀ x, D (L.comp ((T (A.chart i z)).comp
      (gaugeNormalizedHessian f Ks (A.chart i z)))) = 0 := by
    intro L
    rw [← hbase]
    exact hD L
  have h2 := probeAtlas_native_derivative_bound A hA (probe.map t u) (probe.slice_smooth t u)
    probe.constant_nonneg (probe.spatial_C3 t ht htt u hu) (show 2 ≤ 3 by norm_num) i z hz
  have h3 := probeAtlas_native_derivative_bound A hA (probe.map t u) (probe.slice_smooth t u)
    probe.constant_nonneg (probe.spatial_C3 t ht htt u hu) (show 3 ≤ 3 by norm_num) i z hz
  rw [hsame.fderiv_eq]
  have h := norm_incidence_hessian_derivative_without_gauge_bound f T Ks (A.chart i z)
    hf hT hTnorm hTL R K hsplit D hD'
    (probeAtlasDerivativeConstant n N 2 * probe.constant)
    (probeAtlasDerivativeConstant n N 3 * probe.constant) Kbound h2 h3 hK
  exact h.trans_eq (by unfold gaugeSpatialBound; ring)

#print axioms ExactProbeFamily.gaugeSpatialBound_nonneg
#print axioms ExactProbeFamily.actual_incidence_source_derivative_without_gauge_bound

end GlobalEmbedding.Upgrade
