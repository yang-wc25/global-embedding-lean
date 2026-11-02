import Upgrade.RankQProbeColumns
import Upgrade.RankQWeightBudget
import Upgrade.RankQDerivativeError

/-!
# Actual returned-weight probes realize the fixed preparation frame

The two duplicate copies are fixed in the global wave list before the probe
provider is called. Their returned weights produce fixed linear coefficients
that simulate the preselected weights 1 and 2 at every source point.
Only raw probe remainders are amplified by the weight-dependent constant.
The moving Schur derivative and the actual leading-field variation are added
after simulation, so their geometric neighborhoods remain weight independent.
-/

noncomputable section
open Function Manifold Module Set GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
attribute [local instance] actualResidualNormedAddCommGroup actualResidualNormedSpace
  actualResidualFiniteDimensional actualJointNorm rankQActualDerivativeNorm

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

private noncomputable local instance rankQSimulationCoordinateNormed (F₀ : M → V) (x : M) :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance rankQSimulationCoordinateNormedSpace (F₀ : M → V) (x : M) :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedSpace

/-- Actual pointwise parameter direction realizing one preparation column.
The fixed weight coefficients are applied after differentiation, as are the
pointwise radial directions. No derivative of either coefficient is taken. -/
def ExactProbeFamily.rankQPreparationDirection
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (labels : (Fin n × Fin 2) → Fin r) (t : ℝ) (z : M) (l : Fin n × Fin 2) :
    ProbeParameters r :=
  ∑ b : Fin 2, rankQWeightSimulationCoeff
      (fun k b ↦ probe.weight (labels (k,b))) rankQPreparationWeights l.1 l.2 b •
    probe.rankQRadialDirection t z (labels (l.1,b))

/-- Full actual probe responses, the fixed-weight simulation and the actual
prepared leading fields give this error against the fixed center frame.
The term delta*‖T‖ is deliberately OUTSIDE the weight multiplier. -/
theorem ExactProbeFamily.rankQ_simulated_current_response
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (labels : (Fin n × Fin 2) → Fin r) (hinj : Injective labels)
    (hlabels : ∀ l, waves (labels l) = p.waves l.1)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (zy : M × M) (hzy : zy ∈ prep.neighborhood)
    (j : Fin A.count) (hy : zy.2 ∈ (A.chart j).source) :
    let hxc := hA.support_subset i (interior_subset hx)
    let B := rankQActualReference F₀ hF₀ x
    let C := projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x zy.1 (probeAtlasNormalizedFrame A hA i x hxc zy.1)
    let D := fderiv ℝ (rankQSchur B) C
    let T := fun k : Fin n ↦ (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
      (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hxc zy.1) ((p.waves k).tensor zy.1))
    let raw := max (4 * ‖D‖ * ((probe.etaB t + probe.constant * ‖u‖) *
          ‖probeAtlasNormalizationSquare A hA i x hxc‖))
        (4 * (probe.etaV t + probe.constant * ‖u‖))
    let lambda := fun k b ↦ probe.weight (labels (k,b))
    let J := actualRankQJointIncidence F₀ hF₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i j x hxc
      (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5))
    (rankQBlockA B C).IsInvertible →
    ∀ l : Fin n × Fin 2,
      ‖fderiv ℝ (fun v ↦ J (v,A.chart i zy.1,A.chart j zy.2)) u
          (probe.rankQPreparationDirection labels t zy.1 l) -
        (D (T l.1), -((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) •
          (p.waves l.1).value zy.1)‖ ≤
      rankQWeightSimulationBound lambda rankQPreparationWeights * raw := by
  intro hxc B C D T raw lambda J hblock l
  have hz : zy.1 ∈ A.support i := interior_subset (prep.support zy hzy)
  have hzs := hA.support_subset i hz
  obtain ⟨hpos,hne⟩ := p.returned_weights A waves labels hinj hlabels probe
  have hraw_nonneg : 0 ≤ raw := by
    apply le_trans _ (le_max_right _ _)
    exact mul_nonneg (by norm_num) (add_nonneg (probe.etaV_nonneg t)
      (mul_nonneg probe.constant_nonneg (norm_nonneg u)))
  let DJ := fderiv ℝ (fun v ↦ J (v,A.chart i zy.1,A.chart j zy.2)) u
  have hraw (b : Fin 2) :
      ‖DJ (probe.rankQRadialDirection t zy.1 (labels (l.1,b))) -
        (D (T l.1), -((lambda l.1 b ^ 2)⁻¹) • (p.waves l.1).value zy.1)‖ ≤ raw := by
    have haway : (waves (labels (l.1,b))).cutoff zy.2 = 0 := by
      rw [hlabels]
      exact (prep.cutoff zy hzy l.1).2
    have h := probe.rankQ_current_principal_response hA t ht htt u hu
      (labels (l.1,b)) i j x hxc zy.1 zy.2 hz hy haway hblock
    simpa only [hlabels] using! h
  have hsim := norm_simulate_fixed_weights_error_le
    (U := B.ker →L[ℝ] B.rangeᗮ) («V» := V) DJ
    (fun b : Fin 2 ↦ probe.rankQRadialDirection t zy.1 (labels (l.1,b)))
    (fun k : Fin n ↦ D (T k)) (fun k : Fin n ↦ (p.waves k).value zy.1)
    lambda rankQPreparationWeights hpos hne l.1 l.2 raw hraw_nonneg hraw
  have hsim' :
      ‖DJ (probe.rankQPreparationDirection labels t zy.1 l) -
        (D (T l.1), -((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) •
          (p.waves l.1).value zy.1)‖ ≤
        rankQWeightSimulationBound lambda rankQPreparationWeights * raw := by
    apply hsim.trans
    calc
      2 * raw * ‖rankQWeightSimulationCoeff lambda rankQPreparationWeights l.1 l.2‖ =
          (2 * ‖rankQWeightSimulationCoeff lambda rankQPreparationWeights l.1 l.2‖) * raw := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (rankQWeightSimulationBound_le lambda rankQPreparationWeights l.1 l.2) hraw_nonneg
  exact hsim'

/-- Full actual probe responses, the fixed-weight simulation and the actual
prepared leading fields give this error against the fixed center frame.
The term delta*‖T‖ is deliberately OUTSIDE the weight multiplier. -/
theorem ExactProbeFamily.rankQ_prepared_parameter_response
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (labels : (Fin n × Fin 2) → Fin r) (hinj : Injective labels)
    (hlabels : ∀ l, waves (labels l) = p.waves l.1)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (zy : M × M) (hzy : zy ∈ prep.neighborhood)
    (j : Fin A.count) (hy : zy.2 ∈ (A.chart j).source) (delta : ℝ) :
    let hxc := hA.support_subset i (interior_subset hx)
    let B := rankQActualReference F₀ hF₀ x
    let C := projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x zy.1 (probeAtlasNormalizedFrame A hA i x hxc zy.1)
    let D := fderiv ℝ (rankQSchur B) C
    let T := fun k : Fin n ↦ (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
      (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hxc zy.1) ((p.waves k).tensor zy.1))
    let raw := max (4 * ‖D‖ * ((probe.etaB t + probe.constant * ‖u‖) *
          ‖probeAtlasNormalizationSquare A hA i x hxc‖))
        (4 * (probe.etaV t + probe.constant * ‖u‖))
    let lambda := fun k b ↦ probe.weight (labels (k,b))
    let J := actualRankQJointIncidence F₀ hF₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i j x hxc
      (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5))
    (rankQBlockA B C).IsInvertible →
    ‖D - rankQNormalBlock B‖ ≤ delta →
    ∀ l : Fin n × Fin 2,
      ‖fderiv ℝ (fun v ↦ J (v,A.chart i zy.1,A.chart j zy.2)) u
          (probe.rankQPreparationDirection labels t zy.1 l) -
        rankQActualPrincipalColumn F₀ hF₀ x ((p.waves l.1).tensor x)
          (-((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (p.waves l.1).value x)‖ ≤
      rankQWeightSimulationBound lambda rankQPreparationWeights * raw +
        delta * ‖T l.1‖ + prep.tolerance / 4 := by
  intro hxc B C D T raw lambda J hblock hD l
  have hz : zy.1 ∈ A.support i := interior_subset (prep.support zy hzy)
  have hzs := hA.support_subset i hz
  let DJ := fderiv ℝ (fun v ↦ J (v,A.chart i zy.1,A.chart j zy.2)) u
  have hsim' := probe.rankQ_simulated_current_response prep labels hinj hlabels
    t ht htt u hu zy hzy j hy hblock l
  have hder := rankQ_pair_derivative_variation_le
    (S := SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)
    (R := B.ker →L[ℝ] B.rangeᗮ) («V» := V)
    D (rankQNormalBlock B) (T l.1)
    (-((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (p.waves l.1).value zy.1) delta hD
  have hgeometry :
      ‖(rankQNormalBlock B (T l.1), -((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) •
          (p.waves l.1).value zy.1) -
        rankQActualPrincipalColumn F₀ hF₀ x ((p.waves l.1).tensor x)
          (-((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (p.waves l.1).value x)‖ ≤
        prep.tolerance / 4 := by
    have h := (prep.principal_variation zy hzy l).le
    simpa only [atlasIncidencePrincipal, (A.chart i).left_inv hzs] using! h
  exact incidence_error_add_reference_variation _ _ _ _ _
    (incidence_error_add_reference_variation _ _ _ _ _ hsim' hder) hgeometry

#print axioms ExactProbeFamily.rankQPreparationDirection
#print axioms ExactProbeFamily.rankQ_simulated_current_response
#print axioms ExactProbeFamily.rankQ_prepared_parameter_response
end GlobalEmbedding.Upgrade
