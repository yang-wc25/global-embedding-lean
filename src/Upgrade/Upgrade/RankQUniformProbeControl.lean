import Upgrade.RankQProbeSmallness
import Upgrade.RankQWeightBudget
import Upgrade.RankQProbeColumns
import Upgrade.CompactRankQSchurPreparation
import Upgrade.IncidenceSpatialBound

/-!
# Uniform actual rank-q budgets from full probes and chosen normal control

One parameter ball and one scale work on the already fixed geometric
neighborhood. The form displacement comes from the original C² probe norm
and the actual Q gap. The source derivative bound comes from original C³ and
the actual spatial derivative of the same chosen Q. No required incidence
rank, arbitrary form field, or post-frequency spatial shrinking is assumed.
-/
noncomputable section
open Function Manifold Module Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
attribute [local instance] actualResidualNormedAddCommGroup actualResidualNormedSpace
  actualResidualFiniteDimensional actualJointNorm rankQActualDerivativeNorm

private theorem rankQ_derivative_norm_nonneg
    {S W : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (B : S →L[ℝ] W) (D : (S →L[ℝ] W) →L[ℝ] B.ker →L[ℝ] B.rangeᗮ) :
    0 ≤ @norm _ (rankQDerivativeNormedAddCommGroup B).toNorm D :=
  @norm_nonneg _ (@SeminormedAddCommGroup.toSeminormedAddGroup _
    (@NormedAddCommGroup.toSeminormedAddCommGroup _ (rankQDerivativeNormedAddCommGroup B))) D

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

private noncomputable local instance rankQUniformCoordinateNormed (F₀ : M → V) (x : M) :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance rankQUniformCoordinateSpace (F₀ : M → V) (x : M) :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedSpace

/-- All quantitative budgets are actual consequences of the complete probe
interface plus the explicitly identified upstream polar-control consequence.
The same spatial neighborhood works for every returned frequency list. -/
theorem RankQSchurPreparedNeighborhood.exists_probe_ball_scale_budgets
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    (hcompact : ∀ i, IsCompact (A.support i))
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQSchurPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves) (control : ChosenProbeNormalControl probe)
    (labels : (Fin n × Fin 2) → Fin r) :
    let hxc := hA.support_subset i (interior_subset hx)
    let B := rankQActualReference F₀ hF₀ x
    let Dbound := ‖rankQNormalBlock B‖ + prep.derivativeTolerance
    let amp := rankQWeightSimulationBound (fun k b ↦ probe.weight (labels (k,b))) rankQPreparationWeights
    let source := Dbound * control.coordinateSpatialBound hA i x hxc
    ∃ rho > 0, rho ≤ probe.radius ∧ ∃ t₀ > 0, t₀ ≤ probe.threshold ∧
      ∀ t, 0 < t → t < t₀ → ∀ u : ProbeParameters r, ‖u‖ < rho →
      ∀ zy ∈ prep.neighborhood,
      let C := fun s ↦ actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hxc (u,s)
      ‖C (A.chart i zy.1) - normalizedReferenceForm A hA F₀ i x hxc zy.1‖ < prep.formBall.radius / 2 ∧
      ‖(fderiv ℝ (rankQSchur B) (C (A.chart i zy.1))).comp
        (fderiv ℝ C (A.chart i zy.1))‖ ≤ source ∧
      amp * max (4 * Dbound * ((probe.etaB t + probe.constant * ‖u‖) *
          ‖probeAtlasNormalizationSquare A hA i x hxc‖))
        (4 * (probe.etaV t + probe.constant * ‖u‖)) ≤ prep.principal.tolerance / 4 ∧
      max (|t ^ ((56 : ℝ) / 5) / t ^ ((44 : ℝ) / 5)| * source)
        (probeAtlasDerivativeConstant n N 1 * (probe.constant * t ^ ((44 : ℝ) / 5)) +
          prep.principal.tolerance / 4) ≤ prep.principal.tolerance := by
  intro hxc B Dbound amp source
  have hDnonneg : 0 ≤ Dbound :=
    add_nonneg (rankQ_derivative_norm_nonneg B (rankQNormalBlock B)) prep.derivativeTolerance_pos.le
  have hsource : 0 ≤ source := mul_nonneg hDnonneg
    (control.coordinateSpatialBound_nonneg hA i x hxc)
  have hjet : 0 ≤ probeAtlasDerivativeConstant n N 1 * probe.constant :=
    mul_nonneg (probeAtlasDerivativeConstant_nonneg n N 1) probe.constant_nonneg
  obtain ⟨rho, hrho, hrhoBound, tau, htau, htauBound, hsmall⟩ :=
    rankQ_exists_probe_response_ball_scale probe.etaB probe.etaV
      probe.etaB_tendsto probe.etaV_tendsto probe.etaB_nonneg probe.etaV_nonneg
      probe.radius probe.threshold prep.principal.tolerance amp Dbound
      ‖probeAtlasNormalizationSquare A hA i x hxc‖ probe.constant source
      (probeAtlasDerivativeConstant n N 1 * probe.constant)
      probe.radius_pos probe.threshold_pos prep.principal.tolerance_pos
      (rankQWeightSimulationBound_pos _ _) hDnonneg (norm_nonneg _) probe.constant_nonneg hsource hjet
  obtain ⟨tauForm, htauForm, htauFormBound, hclose⟩ :=
    control.eventually_actual_form_close hA hcompact i x hxc
      (div_pos prep.formBall.radius_pos (by norm_num : (0 : ℝ) < 2))
  refine ⟨rho, hrho, hrhoBound, min tau tauForm, lt_min htau htauForm,
    (min_le_left _ _).trans htauBound, ?_⟩
  intro t ht htt u hu zy hzy
  intro C
  have huFull := hu.trans_le hrhoBound
  have htFull := htt.trans_le ((min_le_left _ _).trans htauBound)
  have hz : zy.1 ∈ A.support i :=
    interior_subset (prep.principal.support zy (prep.subset_principal hzy))
  have hnew := hclose t ht (htt.trans_le (min_le_right _ _)) u huFull zy.1 hz
  have hnear : ‖C (A.chart i zy.1) - B‖ < prep.formBall.radius := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (C (A.chart i zy.1))
      (normalizedReferenceForm A hA F₀ i x hxc zy.1) B
    have href := prep.reference_variation zy hzy
    linarith
  have hDn := (prep.formBall.spec (C (A.chart i zy.1)) hnear).2.2.2.1
  have hCn := control.actual_coordinate_spatial_bound hA i x hxc t ht htFull u huFull zy.1 hz
  have hK : ‖(fderiv ℝ (rankQSchur B) (C (A.chart i zy.1))).comp
      (fderiv ℝ C (A.chart i zy.1))‖ ≤ source := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hDn hCn (norm_nonneg _) hDnonneg)
  have hbud := hsmall t ht (htt.trans_le (min_le_left _ _)) ‖u‖ (norm_nonneg u) hu
  refine ⟨hnew, hK, hbud.1, ?_⟩
  simpa only [mul_assoc] using hbud.2

#print axioms RankQSchurPreparedNeighborhood.exists_probe_ball_scale_budgets
end GlobalEmbedding.Upgrade
