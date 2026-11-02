import Main.GeneralLegalWaveAtlasFields

/-!
# Full paired-probe output for arbitrary supported smooth cutoffs

Every field is the literal old native quantitative contract, now quantified
over `OpenSupportedLegalWave`, which permits the paper's arbitrary cutoff.
The actual geometric family, orthogonal normal identification and identified
true second form are unchanged. This is an output record only, not an
existence assumption or a new final theorem.
-/
noncomputable section
open Bundle Filter Manifold Set GlobalEmbedding.Paper
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.Continuation
open Upgrade SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The original quantitative probe contract, extending the same actual geometry.
This separation makes the object/estimate distinction explicit; no estimate is
replaced by a conclusion about incidence rank. -/
structure GeneralExactProbeFamily
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (A : BufferedAtlas M E) {r : ℕ} (waves : Fin r → OpenSupportedLegalWave F₀ hF₀)
    extends ProbeGeometry (n := n) F₀ r where
  weight : Fin r → ℝ
  weight_pos : ∀ l, 0 < weight l
  distinct_on_overlap : ∀ l k, l ≠ k →
    (tsupport (waves l).cutoff ∩ tsupport (waves k).cutoff).Nonempty → weight l ≠ weight k
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  etaB : ℝ → ℝ
  etaV : ℝ → ℝ
  etaB_nonneg : ∀ t, 0 ≤ etaB t
  etaV_nonneg : ∀ t, 0 ≤ etaV t
  etaB_tendsto : Tendsto etaB (𝓝[>] 0) (𝓝 0)
  etaV_tendsto : Tendsto etaV (𝓝[>] 0) (𝓝 0)
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
  secondForm_response : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    ∀ l b i x, x ∈ A.support i →
      ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i x)
          (identifiedTrueSecondForm (n := n) F₀ (map t v) (slice_smooth t v)
          (normalIdentification t v) x)) u (Pi.single (l, b) 1) -
        (t ^ ((44 : ℝ) / 5) * probeTrig b (weight l * (waves l).phase x /
          t ^ ((6 : ℝ) / 5))) •
          probeTensorInFrame (probeAtlasFrame A i x) ((waves l).tensor x)‖ ≤
        t ^ ((44 : ℝ) / 5) * (etaB t + constant * ‖u‖)
  value_response : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    ∀ l b x,
      ‖fderiv ℝ (fun v ↦ map t v x) u (Pi.single (l, b) 1) -
        (-(t ^ ((56 : ℝ) / 5)) * (weight l ^ 2)⁻¹ *
          probeTrig b (weight l * (waves l).phase x / t ^ ((6 : ℝ) / 5))) •
          (waves l).value x‖ ≤
        t ^ ((56 : ℝ) / 5) * (etaV t + constant * ‖u‖)


namespace GeneralExactProbeFamily

/-- The broader output specializes to the frozen upgrade wave class without
changing the actual map, normal identification, constants or domains. -/
def toLocalFamily [T2Space M]
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ}
    {waves : Fin r → LocalLegalWave F₀ hF₀}
    (d : GeneralExactProbeFamily F₀ hF₀ A (fun l => OpenSupportedLegalWave.ofLocal (waves l))) :
    ExactProbeFamily F₀ hF₀ A waves where
  toProbeGeometry := d.toProbeGeometry
  weight := d.weight
  weight_pos := d.weight_pos
  distinct_on_overlap := d.distinct_on_overlap
  constant := d.constant
  constant_nonneg := d.constant_nonneg
  etaB := d.etaB
  etaV := d.etaV
  etaB_nonneg := d.etaB_nonneg
  etaV_nonneg := d.etaV_nonneg
  etaB_tendsto := d.etaB_tendsto
  etaV_tendsto := d.etaV_tendsto
  closeness := d.closeness
  spatial_C3 := d.spatial_C3
  parameter_C1 := d.parameter_C1
  parameter_C2 := d.parameter_C2
  secondForm_response := d.secondForm_response
  value_response := d.value_response

@[simp] theorem toLocalFamily_geometry [T2Space M]
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ,V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ}
    {waves : Fin r → LocalLegalWave F₀ hF₀}
    (d : GeneralExactProbeFamily F₀ hF₀ A (fun l => OpenSupportedLegalWave.ofLocal (waves l))) :
    d.toLocalFamily.toProbeGeometry = d.toProbeGeometry := rfl

end GeneralExactProbeFamily
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.GeneralExactProbeFamily.toLocalFamily
