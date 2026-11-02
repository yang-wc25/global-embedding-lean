import Upgrade.IncidenceSupportedProbeData
import Upgrade.CompactSupportedJointPreparation
import Upgrade.RankQWeightBudget

/-!
# Returned-weight actual probes realize the fixed supported joint frame

The same finite packet was prepared with auxiliary weights 1 and 2 before
the global list and returned weights. The already verified two-copy inverse
is applied to the actual current-derivative columns. Only raw probe errors
are multiplied by its fixed coefficient bound. The current equation change
and actual leading-field variation are then added separately.
-/

noncomputable section
open Function Manifold Module Set GlobalEmbedding.Offline
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

private noncomputable local instance supportedSimulationFormNormed (F₀ : M → V) (x : M) :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance supportedSimulationFormSpace (F₀ : M → V) (x : M) :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedSpace

theorem SupportedJointWavePacket.returned_weights
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    (p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y)
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (labels : (Fin (n * (n - 1) / 2 + n) × Fin 2) → Fin r)
    (hinj : Injective labels) (hlabels : ∀ l, waves (labels l) = p.waves l.1) :
    (∀ l b, 0 < probe.weight (labels (l, b))) ∧
      (∀ l, probe.weight (labels (l, 0)) ≠ probe.weight (labels (l, 1))) := by
  have hs (l : Fin (n * (n - 1) / 2 + n)) (b : Fin 2) :
      x ∈ tsupport ((waves (labels (l, b))).cutoff : M → ℝ) := by
    apply subset_tsupport
    change (waves (labels (l, b))).cutoff x ≠ 0
    rw [hlabels, p.one_near.self_of_nhds l]
    exact one_ne_zero
  refine ⟨fun l b ↦ probe.weight_pos _, ?_⟩
  intro l
  apply probe.distinct_on_overlap
  · intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd (hinj h))
  · exact ⟨x, hs l 0, hs l 1⟩

/-- A literal parameter vector, selected only after differentiating. -/
def ExactProbeFamily.supportedPreparationDirection
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (labels : (Fin (n * (n - 1) / 2 + n) × Fin 2) → Fin r)
    (t : ℝ) (z : M) (l : Fin (n * (n - 1) / 2 + n) × Fin 2) : ProbeParameters r :=
  ∑ b : Fin 2, rankQWeightSimulationCoeff
    (fun k b ↦ probe.weight (labels (k,b))) rankQPreparationWeights l.1 l.2 b •
      pairedRadialDirection
        (probe.weight (labels (l.1,b)) * (waves (labels (l.1,b))).phase z / t ^ ((6 : ℝ) / 5))
        (Pi.single (labels (l.1,b), false) 1) (Pi.single (labels (l.1,b), true) 1)

/-- The actual normalized parameter derivative is close to the fixed
geometric center column. The geometric derivative error is outside the
weight coefficient bound, so the preselected neighborhood is unchanged. -/
theorem SupportedJointPreparedNeighborhood.actual_prepared_parameter_response
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
    (j : Fin A.count) (hy : zy.2 ∈ (A.chart j).source) (delta : ℝ) :
    let hxc := hA.support_subset i (interior_subset hx)
    let B := LinearMap.toContinuousLinearMap
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)
    let C := projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x zy.1 (probeAtlasNormalizedFrame A hA i x hxc zy.1)
    let D := fderiv ℝ p.chart.equation C
    let T := fun k : Fin (n * (n - 1) / 2 + n) ↦
      (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
        (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hxc zy.1) ((p.waves k).tensor zy.1))
    let raw := max (4 * ‖D‖ * ((probe.etaB t + probe.constant * ‖u‖) *
      ‖probeAtlasNormalizationSquare A hA i x hxc‖)) (4 * (probe.etaV t + probe.constant * ‖u‖))
    let lambda := fun k b ↦ probe.weight (labels (k,b))
    let data := p.probeData hA i hxc probe t j
    C ∈ p.chart.domain → ‖D - fderiv ℝ p.chart.equation B‖ ≤ delta →
    ∀ l : Fin (n * (n - 1) / 2 + n) × Fin 2,
      ‖fderiv ℝ (fun v ↦ data.incidence (v, A.chart i zy.1, A.chart j zy.2)) u
          (probe.supportedPreparationDirection labels t zy.1 l) -
        supportedJointPrincipalColumn (incidenceActualTangent (n := n) F₀ x)
          p.equationColumns p.valueNormals rankQPreparationWeights l‖ ≤
      rankQWeightSimulationBound lambda rankQPreparationWeights * raw +
        delta * ‖T l.1‖ + prep.tolerance / 4 := by
  intro hxc B C D T raw lambda data hdom hD l
  have hz : zy.1 ∈ A.support i := interior_subset (prep.support zy hzy)
  have hzs := hA.support_subset i hz
  obtain ⟨hpos, hne⟩ := p.returned_weights probe labels hinj hlabels
  have hraw_nonneg : 0 ≤ raw := by
    exact (mul_nonneg (by norm_num) (add_nonneg (probe.etaV_nonneg t)
      (mul_nonneg probe.constant_nonneg (norm_nonneg u)))).trans (le_max_right _ _)
  let DJ := fderiv ℝ (fun v ↦ data.incidence (v, A.chart i zy.1, A.chart j zy.2)) u
  let dirs : Fin 2 → ProbeParameters r := fun b ↦ pairedRadialDirection
    (probe.weight (labels (l.1,b)) * (waves (labels (l.1,b))).phase zy.1 / t ^ ((6 : ℝ) / 5))
    (Pi.single (labels (l.1,b), false) 1) (Pi.single (labels (l.1,b), true) 1)
  have hraw (b : Fin 2) :
      ‖DJ (dirs b) - (D (T l.1), -((lambda l.1 b ^ 2)⁻¹) • (p.waves l.1).value zy.1)‖ ≤ raw := by
    have haway : (waves (labels (l.1,b))).cutoff zy.2 = 0 := by
      rw [hlabels]
      exact (prep.cutoff zy hzy l.1).2
    have h := p.current_principal_response hA i hxc probe t ht htt u hu
      (labels (l.1,b)) j zy.1 zy.2 hz hy haway hdom
    simpa only [DJ, dirs, data, D, C, T, raw, lambda, hlabels] using! h
  have hsim := norm_simulate_fixed_weights_error_le
    (U := Fin p.chart.codim → ℝ) («V» := V) DJ dirs
    (fun k ↦ D (T k)) (fun k ↦ (p.waves k).value zy.1)
    lambda rankQPreparationWeights hpos hne l.1 l.2 raw hraw_nonneg hraw
  have hsim' :
      ‖DJ (probe.supportedPreparationDirection labels t zy.1 l) -
        (D (T l.1), -((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (p.waves l.1).value zy.1)‖ ≤
      rankQWeightSimulationBound lambda rankQPreparationWeights * raw := by
    apply hsim.trans
    calc
      2 * raw * ‖rankQWeightSimulationCoeff lambda rankQPreparationWeights l.1 l.2‖ =
          (2 * ‖rankQWeightSimulationCoeff lambda rankQPreparationWeights l.1 l.2‖) * raw := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (rankQWeightSimulationBound_le lambda rankQPreparationWeights l.1 l.2) hraw_nonneg
  have hdelta : 0 ≤ delta := (norm_nonneg _).trans hD
  have hder : ‖(D (T l.1), -((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (p.waves l.1).value zy.1) -
      (fderiv ℝ p.chart.equation B (T l.1),
        -((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (p.waves l.1).value zy.1)‖ ≤ delta * ‖T l.1‖ := by
    apply norm_prod_le_iff.mpr
    constructor
    · exact (ContinuousLinearMap.le_opNorm (D - fderiv ℝ p.chart.equation B) (T l.1)).trans
        (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
    · simpa only [Prod.snd_sub, Prod.snd, sub_self, norm_zero] using mul_nonneg hdelta (norm_nonneg (T l.1))
  have hgeometry :
      ‖(fderiv ℝ p.chart.equation B (T l.1),
          -((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (p.waves l.1).value zy.1) -
        supportedJointPrincipalColumn (incidenceActualTangent (n := n) F₀ x)
          p.equationColumns p.valueNormals rankQPreparationWeights l‖ ≤ prep.tolerance / 4 := by
    have h := (prep.principal_variation zy hzy l).le
    simpa only [atlasIncidencePrincipal, (A.chart i).left_inv hzs] using! h
  exact incidence_error_add_reference_variation _ _ _ _ _
    (incidence_error_add_reference_variation _ _ _ _ _ hsim' hder) hgeometry

#print axioms SupportedJointWavePacket.returned_weights
#print axioms SupportedJointPreparedNeighborhood.actual_prepared_parameter_response

end GlobalEmbedding.Upgrade
