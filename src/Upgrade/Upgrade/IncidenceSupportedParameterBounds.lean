import Upgrade.IncidenceFormNorms
import Upgrade.IncidenceSupportedProbeSimulation

/-! The fixed supported equation ball supplies the actual domain and
derivative margin. Only the true probe response is amplified by the returned
weight coefficient, after which fixed geometric errors use their old budget. -/

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

theorem SupportedJointPreparedNeighborhood.exact_probe_parameter_bounds
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : SupportedJointPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (labels : (Fin (n * (n - 1) / 2 + n) × Fin 2) → Fin r)
    (hinj : Injective labels) (hlabels : ∀ l, waves (labels l) = p.waves l.1)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (zy : M × M) (hzy : zy ∈ prep.neighborhood)
    (j : Fin A.count) (hy : zy.2 ∈ (A.chart j).source) :
    let hxc := hA.support_subset i (interior_subset hx)
    let B := LinearMap.toContinuousLinearMap
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)
    let C := projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x zy.1 (probeAtlasNormalizedFrame A hA i x hxc zy.1)
    let Dmax := ‖fderiv ℝ p.chart.equation B‖ + prep.derivativeTolerance
    let amp := rankQWeightSimulationBound (fun k b ↦ probe.weight (labels (k,b))) rankQPreparationWeights
    let data := p.probeData hA i hxc probe t j
    ‖C - normalizedReferenceForm A hA F₀ i x hxc zy.1‖ ≤ prep.formBall.radius / 2 →
    amp * max (4 * Dmax * ((probe.etaB t + probe.constant * ‖u‖) *
        ‖probeAtlasNormalizationSquare A hA i x hxc‖))
      (4 * (probe.etaV t + probe.constant * ‖u‖)) ≤ prep.tolerance / 4 →
    C ∈ p.chart.domain ∧ ‖fderiv ℝ p.chart.equation C‖ ≤ Dmax ∧
      ∀ l,
        ‖fderiv ℝ (fun v ↦ data.incidence (v,A.chart i zy.1,A.chart j zy.2)) u
          (probe.supportedPreparationDirection labels t zy.1 l) -
          supportedJointPrincipalColumn (incidenceActualTangent (n := n) F₀ x)
            p.equationColumns p.valueNormals rankQPreparationWeights l‖ ≤ prep.tolerance := by
  intro hxc B C Dmax amp data hnew hbudget
  have hclose : ‖C - B‖ < prep.formBall.radius :=
    (norm_sub_le_norm_sub_add_norm_sub C
      (normalizedReferenceForm A hA F₀ i x hxc zy.1) B).trans_lt
      (by linarith [prep.reference_variation zy hzy])
  obtain ⟨hdom, hR, hD, hDn⟩ := prep.formBall.spec C hclose
  refine ⟨hdom, hDn, ?_⟩
  intro l
  have hr := prep.actual_prepared_parameter_response probe labels hinj hlabels
    t ht htt u hu zy hzy j hy prep.derivativeTolerance hdom hD.le l
  have hraw_nonneg : 0 ≤ (probe.etaB t + probe.constant * ‖u‖) *
      ‖probeAtlasNormalizationSquare A hA i x hxc‖ :=
    mul_nonneg (add_nonneg (probe.etaB_nonneg t)
      (mul_nonneg probe.constant_nonneg (norm_nonneg _))) (norm_nonneg _)
  have hraw := max_le_max
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDn (by norm_num : (0 : ℝ) ≤ 4)) hraw_nonneg)
    (le_refl (4 * (probe.etaV t + probe.constant * ‖u‖)))
  have hamp : 0 ≤ amp := (rankQWeightSimulationBound_pos _ _).le
  have hp : amp * max (4 * ‖fderiv ℝ p.chart.equation C‖ *
        ((probe.etaB t + probe.constant * ‖u‖) * ‖probeAtlasNormalizationSquare A hA i x hxc‖))
        (4 * (probe.etaV t + probe.constant * ‖u‖)) ≤ prep.tolerance / 4 :=
    (mul_le_mul_of_nonneg_left hraw hamp).trans hbudget
  have hd := (mul_le_mul_of_nonneg_left (prep.tensor_bound zy hzy l.1)
    prep.derivativeTolerance_pos.le).trans prep.derivative_budget
  exact hr.trans (by linarith [prep.tolerance_pos])

#print axioms SupportedJointPreparedNeighborhood.exact_probe_parameter_bounds
end GlobalEmbedding.Upgrade
