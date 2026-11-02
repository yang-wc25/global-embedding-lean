import Round2.SupportedJointGapRank
import Round2.ProbeNormalGap
import Upgrade.RankQProbeSmallness

/-!
# One parameter ball and scale for actual supported-coincidence rank

The source bound is obtained from the reference immersion's genuine compact
metric left inverse. The only normal-identification estimate is the selected
Qop gap. Domain membership holds throughout the unchanged prepared region;
joint rank is proved at its actual supported points, where gauge cancellation
is valid. No all-domain derivative bound or rank premise is introduced.
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
attribute [local instance] incidenceActualFormNormed incidenceActualFormSpace

/-- A fixed original legal packet and the same full probe family give one
positive parameter ball and one scale. The actual supported equation's domain
is protected everywhere; its actual joint derivative rank is asserted only
where the current true second form has a supported kernel. -/
theorem SupportedJointPreparedNeighborhood.exists_uniform_probe_domain_rank_of_gap
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    (hcompact : ∀ i, IsCompact (A.support i))
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    (himm₀ : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    {x y₀ : M}
    {p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : SupportedJointPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves) (control : ChosenProbeNormalGap probe)
    (labels : (Fin (n * (n - 1) / 2 + n) × Fin 2) → Fin r)
    (hinj : Injective labels) (hlabels : ∀ l, waves (labels l) = p.waves l.1) :
    ∃ ρ > 0, ρ ≤ probe.radius ∧ ∃ t₀ > 0, t₀ ≤ probe.threshold ∧
      ∀ t, 0 < t → t < t₀ → ∀ u : ProbeParameters r, ‖u‖ < ρ →
      ∀ zy ∈ prep.neighborhood, ∀ j : Fin A.count, zy.2 ∈ (A.chart j).source →
      actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x (hA.support_subset i (interior_subset hx))
        (u,A.chart i zy.1) ∈ p.chart.domain ∧
      (HasSupportedKernel (trueSecondForm (probe.map t u) (probe.slice_smooth t u) zy.1) →
        prep.ActualProbeJointRank probe t u zy j) := by
  let hxc := hA.support_subset i (interior_subset hx)
  let B := LinearMap.toContinuousLinearMap
    (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)
  let Dmax := ‖fderiv ℝ p.chart.equation B‖ + prep.derivativeTolerance
  have hDmax : 0 ≤ Dmax := add_nonneg (norm_nonneg _) prep.derivativeTolerance_pos.le
  let amp := rankQWeightSimulationBound (fun k b ↦ probe.weight (labels (k,b))) rankQPreparationWeights
  obtain ⟨Kbound, hKpos, hKbound⟩ := exists_uniform_sameMetric_tangentLeftInverse_bound
    A hA hcompact F₀ hF₀ himm₀
  let source := Dmax * probe.gaugeSpatialBound hA i x hxc Kbound
  have hsource : 0 ≤ source := mul_nonneg hDmax
    (probe.gaugeSpatialBound_nonneg hA i x hxc hKpos.le)
  let jet := probeAtlasDerivativeConstant n N 1 * probe.constant
  have hjet : 0 ≤ jet := mul_nonneg (probeAtlasDerivativeConstant_nonneg n N 1)
    probe.constant_nonneg
  obtain ⟨ρ, hρ, hρrad, tB, htB, htBtop, hbud⟩ := rankQ_exists_probe_response_ball_scale
    probe.etaB probe.etaV probe.etaB_tendsto probe.etaV_tendsto
    probe.etaB_nonneg probe.etaV_nonneg probe.radius probe.threshold prep.tolerance amp Dmax
    ‖probeAtlasNormalizationSquare A hA i x hxc‖ probe.constant source jet
    probe.radius_pos probe.threshold_pos prep.tolerance_pos (rankQWeightSimulationBound_pos _ _)
    hDmax (norm_nonneg _) probe.constant_nonneg hsource hjet
  obtain ⟨tF, htF, htFtop, hform⟩ := control.eventually_actual_form_close hA hcompact
    i x hxc (half_pos prep.formBall.radius_pos)
  refine ⟨ρ, hρ, hρrad, min tB tF, lt_min htB htF,
    (min_le_left _ _).trans htBtop, ?_⟩
  intro t ht htt u hu zy hzy j hy
  have htBt := htt.trans_le (min_le_left tB tF)
  have htFt := htt.trans_le (min_le_right tB tF)
  have httop := htBt.trans_le htBtop
  have huprobe := hu.trans_le hρrad
  have hz : zy.1 ∈ A.support i := interior_subset (prep.support zy hzy)
  have hzs := hA.support_subset i hz
  let C := actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
    (probe.normalIdentification t) A hA i x hxc (u,A.chart i zy.1)
  let C' := projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
    (probe.normalIdentification t u) x zy.1 (probeAtlasNormalizedFrame A hA i x hxc zy.1)
  have hC : C = C' := by
    dsimp only [C, actualSupportedProbeCoordinate]
    rw [(A.chart i).left_inv hzs]
  have hnew : ‖C - normalizedReferenceForm A hA F₀ i x hxc zy.1‖ ≤
      prep.formBall.radius / 2 := (hform t ht htFt u huprobe zy.1 hz).le
  have hclose : ‖C - B‖ < prep.formBall.radius :=
    (norm_sub_le_norm_sub_add_norm_sub C
      (normalizedReferenceForm A hA F₀ i x hxc zy.1) B).trans_lt
      (by linarith [prep.reference_variation zy hzy])
  have hdom := (prep.formBall.spec C hclose).1
  refine ⟨hdom, ?_⟩
  intro hsupported
  have hgap : ‖(normalSpace (I := IM) F₀ ((A.chart i).symm (A.chart i zy.1))).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1 := by
    rw [(A.chart i).left_inv hzs]
    exact (prep.normal_gap zy hzy).trans (by norm_num)
  have hzero : p.chart.equation C = 0 :=
    (actualSupportedProbeCoordinate_equation_zero_iff F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hxc (u,A.chart i zy.1)
      ((A.chart i).map_source hzs) hgap _ p.chart hdom).mpr
        (by
          let supportPred : M → Prop := fun z ↦ HasSupportedKernel
            (trueSecondForm (probe.map t u) (probe.slice_smooth t u) z)
          exact (congrArg supportPred ((A.chart i).left_inv hzs)).mpr hsupported)
  have hK := hKbound (probe.map t u) (probe.slice_smooth t u)
    (probe.metric t ht httop u huprobe) i zy.1 hz
  have hbudgets := hbud t ht htBt ‖u‖ (norm_nonneg _) hu
  have hsourceBudget : max (|t ^ ((56 : ℝ) / 5) / t ^ ((44 : ℝ) / 5)| *
        (Dmax * probe.gaugeSpatialBound hA i x hxc Kbound))
      (probeAtlasDerivativeConstant n N 1 *
        (probe.constant * t ^ ((44 : ℝ) / 5)) + prep.tolerance / 4) ≤ prep.tolerance := by
    simpa only [jet, mul_assoc] using hbudgets.2
  apply prep.exact_probe_joint_rank_at_supported_zero himm₀ probe labels hinj hlabels
    t ht httop u huprobe zy hzy j hy Kbound hK
  · change ‖C' - normalizedReferenceForm A hA F₀ i x hxc zy.1‖ ≤ prep.formBall.radius / 2
    rw [← hC]
    exact hnew
  · exact hbudgets.1
  · exact hsourceBudget
  · change p.chart.equation C' = 0
    rw [← hC]
    exact hzero

#print axioms SupportedJointPreparedNeighborhood.exists_uniform_probe_domain_rank_of_gap
end GlobalEmbedding.Upgrade
