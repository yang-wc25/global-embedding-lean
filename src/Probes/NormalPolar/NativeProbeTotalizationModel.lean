import NormalPolar.NativeProbeTotalization
import NormalPolar.FullResponseModelData

/-!
# A domain-only model/repair input for the full original probes

Only the actual model, the actual final map on the original admitted domain,
and native correction estimates are supplied. The model need not have the
exact metric. The final-map native responses are first proved by the existing
literal-correction theorems. The explicit reference extension then supplies
total smooth slices and total immersion and constructs the same polar Q.

No new outside-map hypothesis, parameter domain or response constant is
introduced. Existence and bounds for the actual repair remain upstream.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- The genuine model and final-map data, without requirements on total
outside slices. All norms and derivatives are those of the actual given maps. -/
structure NativeProbeDomainModelData
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    {r : ℕ} (waves : Fin r → LocalLegalWave F₀ hF₀) where
  radius : ℝ
  radius_pos : 0 < radius
  threshold : ℝ
  threshold_pos : 0 < threshold
  map : ℝ → ProbeParameters r → M → V
  model : ℝ → ProbeParameters r → M → V
  joint_smooth : ∀ t, 0 < t → t < threshold →
    ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry (map t)) (Metric.ball 0 radius ×ˢ univ)
  model_joint_smooth : ∀ t, 0 < t → t < threshold →
    ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry (model t)) (Metric.ball 0 radius ×ˢ univ)
  metric : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
    inducedMetric (I := IM) (map t u) x = inducedMetric (I := IM) F₀ x
  weight : Fin r → ℝ
  weight_pos : ∀ l, 0 < weight l
  distinct_on_overlap : ∀ l k, l ≠ k →
    (tsupport (waves l).cutoff ∩ tsupport (waves k).cutoff).Nonempty → weight l ≠ weight k
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  modelHConstant : ℝ
  tailHConstant : ℝ
  modelVConstant : ℝ
  tailVConstant : ℝ
  modelHConstant_nonneg : 0 ≤ modelHConstant
  tailHConstant_nonneg : 0 ≤ tailHConstant
  modelVConstant_nonneg : 0 ≤ modelVConstant
  tailVConstant_nonneg : 0 ≤ tailVConstant
  hessian_coefficient_le : modelHConstant + probeAtlasDerivativeConstant n N 2 * tailHConstant ≤ constant
  value_coefficient_le : modelVConstant + nativeValueTailConstant N * tailVConstant ≤ constant
  etaModelH : ℝ → ℝ
  etaTailH : ℝ → ℝ
  etaModelV : ℝ → ℝ
  etaTailV : ℝ → ℝ
  etaModelH_nonneg : ∀ t, 0 ≤ etaModelH t
  etaTailH_nonneg : ∀ t, 0 ≤ etaTailH t
  etaModelV_nonneg : ∀ t, 0 ≤ etaModelV t
  etaTailV_nonneg : ∀ t, 0 ≤ etaTailV t
  etaModelH_tendsto : Tendsto etaModelH (𝓝[>] 0) (𝓝 0)
  etaTailH_tendsto : Tendsto etaTailH (𝓝[>] 0) (𝓝 0)
  etaModelV_tendsto : Tendsto etaModelV (𝓝[>] 0) (𝓝 0)
  etaTailV_tendsto : Tendsto etaTailV (𝓝[>] 0) (𝓝 0)
  closeness : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    probeAtlasCj A 2 (map t u - F₀) ≤ ENNReal.ofReal (constant * t ^ ((44 : ℝ) / 5))
  spatial_C3 : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    probeAtlasCj A 3 (map t u) ≤ ENNReal.ofReal constant
  parameter_C1 : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ d,
    probeAtlasCj A 1 (fun x ↦ fderiv ℝ (fun v ↦ map t v x) u d) ≤
      ENNReal.ofReal (constant * t ^ (10 : ℕ) * ‖d‖)
  parameter_C2 : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ d,
    probeAtlasCj A 2 (fun x ↦ fderiv ℝ (fun v ↦ map t v x) u d) ≤
      ENNReal.ofReal (constant * t ^ ((44 : ℝ) / 5) * ‖d‖)
  model_hessian_response : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    ∀ l b i x, x ∈ A.support i →
      ‖fderiv ℝ
          (fun v ↦ fderiv ℝ (fderiv ℝ (model t v ∘ (A.chart i).symm)) (A.chart i x))
          u (Pi.single (l, b) 1) -
        (t ^ ((44 : ℝ) / 5) * probeTrig b (weight l * (waves l).phase x /
          t ^ ((6 : ℝ) / 5))) •
          phaseRankOneHessian ((waves l).phase ∘ (A.chart i).symm)
            ((waves l).value ∘ (A.chart i).symm) (A.chart i x)‖ ≤
        t ^ ((44 : ℝ) / 5) * (etaModelH t + modelHConstant * ‖u‖)
  model_value_response : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    ∀ l b x,
      ‖fderiv ℝ (fun v ↦ model t v x) u (Pi.single (l, b) 1) -
        (-(t ^ ((56 : ℝ) / 5)) * (weight l ^ 2)⁻¹ *
          probeTrig b (weight l * (waves l).phase x / t ^ ((6 : ℝ) / 5))) •
          (waves l).value x‖ ≤
        t ^ ((56 : ℝ) / 5) * (etaModelV t + modelVConstant * ‖u‖)
  hessian_tail : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ l b,
    probeAtlasCj A 2
      (fun y ↦ fderiv ℝ (fun v ↦ map t v y - model t v y) u (Pi.single (l, b) 1)) ≤
        ENNReal.ofReal (t ^ ((44 : ℝ) / 5) * (etaTailH t + tailHConstant * ‖u‖))
  value_tail : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ l b,
    probeAtlasCj A 0
      (fun y ↦ fderiv ℝ (fun v ↦ map t v y - model t v y) u (Pi.single (l, b) 1)) ≤
        ENNReal.ofReal (t ^ ((56 : ℝ) / 5) * (etaTailV t + tailVConstant * ‖u‖))
  reserve : ℝ
  reserve_lt_one : reserve < 1
  closeness_reserve : ∀ t, 0 < t → t < threshold →
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ u, ‖u‖ < radius →
        probeAtlasCj A 2 (fun x ↦ map t u x - F₀ x) ≤ ENNReal.ofReal b) ∧
      originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀ * b ≤ reserve

namespace NativeProbeDomainModelData

variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A}
    {hcompact : ∀ i, IsCompact (A.support i)}
    {hcover : ∀ x, ∃ i, x ∈ A.support i}
    {hi₀ : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x)}
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}

/-- Prove both final native responses from the true model and literal
correction. This step keeps the actual final map entirely unchanged. -/
def toDomainData
    (d : NativeProbeDomainModelData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    NativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves where
  radius := d.radius
  radius_pos := d.radius_pos
  threshold := d.threshold
  threshold_pos := d.threshold_pos
  map := d.map
  joint_smooth := d.joint_smooth
  metric := d.metric
  weight := d.weight
  weight_pos := d.weight_pos
  distinct_on_overlap := d.distinct_on_overlap
  constant := d.constant
  constant_nonneg := d.constant_nonneg
  etaH := nativeHessianTailModulus n N d.etaModelH d.etaTailH
  etaV := nativeValueTailModulus N d.etaModelV d.etaTailV
  etaH_nonneg := nativeHessianTailModulus_nonneg n N d.etaModelH d.etaTailH
    d.etaModelH_nonneg d.etaTailH_nonneg
  etaV_nonneg := nativeValueTailModulus_nonneg N d.etaModelV d.etaTailV
    d.etaModelV_nonneg d.etaTailV_nonneg
  etaH_tendsto := nativeHessianTailModulus_tendsto n N d.etaModelH d.etaTailH
    d.etaModelH_tendsto d.etaTailH_tendsto
  etaV_tendsto := nativeValueTailModulus_tendsto N d.etaModelV d.etaTailV
    d.etaModelV_tendsto d.etaTailV_tendsto
  closeness := d.closeness
  spatial_C3 := d.spatial_C3
  parameter_C1 := d.parameter_C1
  parameter_C2 := d.parameter_C2
  native_hessian_response := nativeProbe_hessian_response_of_originalC2_correction
    A hA hcover waves d.weight d.map d.model d.radius d.threshold d.joint_smooth d.model_joint_smooth
    d.etaModelH d.etaTailH d.modelHConstant d.tailHConstant d.constant d.etaTailH_nonneg
    d.tailHConstant_nonneg d.hessian_coefficient_le d.model_hessian_response d.hessian_tail
  value_response := nativeProbe_value_response_of_originalC0_correction
    A hA hcover waves d.weight d.map d.model d.radius d.threshold d.joint_smooth d.model_joint_smooth
    d.etaModelV d.etaTailV d.modelVConstant d.tailVConstant d.constant d.etaTailV_nonneg
    d.tailVConstant_nonneg d.value_coefficient_le d.model_value_response d.value_tail
  reserve := d.reserve
  reserve_lt_one := d.reserve_lt_one
  closeness_reserve := d.closeness_reserve

/-- Construct the full original probe, selecting only the otherwise
unprescribed outside values of the final family. -/
def toExactProbeFamily [T2Space M]
    (d : NativeProbeDomainModelData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    ExactProbeFamily F₀ hF₀ A waves := d.toDomainData.toExactProbeFamily

/-- The same constructed Q has the gap required by the geometric consumer. -/
def chosenNormalGap [T2Space M]
    (d : NativeProbeDomainModelData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    ChosenProbeNormalGap d.toExactProbeFamily := d.toDomainData.chosenNormalGap

/-- The model-to-final response proof itself leaves all genuine final-map
inputs, radius, threshold, weights and reserve literally unchanged. -/
theorem toDomainData_preserves
    (d : NativeProbeDomainModelData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    d.toDomainData.map = d.map ∧ d.toDomainData.radius = d.radius ∧
      d.toDomainData.threshold = d.threshold ∧ d.toDomainData.weight = d.weight ∧
      d.toDomainData.constant = d.constant ∧ d.toDomainData.reserve = d.reserve :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every actual admitted repaired slice is retained, along with its
parameter ball, scale interval and fixed weights. -/
theorem toExactProbeFamily_preserves_admitted [T2Space M]
    (d : NativeProbeDomainModelData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    d.toExactProbeFamily.radius = d.radius ∧
    d.toExactProbeFamily.threshold = d.threshold ∧
    d.toExactProbeFamily.weight = d.weight ∧
    (∀ t, 0 < t → t < d.threshold → ∀ u, ‖u‖ < d.radius →
      d.toExactProbeFamily.map t u = d.map t u) :=
  d.toDomainData.toExactProbeFamily_preserves_admitted

end NativeProbeDomainModelData
end GlobalEmbedding.NormalPolar
