import NormalPolar.OriginalMapGeometry
import NormalPolar.ResponseUniform

/-!
# Actual map and native jet data before choosing the normal identification

This input contains only the actual mapping family and its original metric,
smoothness and native jet budgets. The native Hessian response uses the same
phase and cutoff-normal value as the original probe interface. No normal
identification, its regularity, its response, or identified-form estimate is
an input. The numerical reserve is expressed in the original C² budget.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- The remaining analytic input uses actual maps and native derivatives.
The fixed atlas and reference immersion determine the reserve constant before
the scale and probe parameter. The reserve uses an actual uniform C² budget,
which can be tighter than the common response constant. All original domains
are supplied unchanged. -/
structure NativeProbeData
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
  slice_smooth : ∀ t u, ContMDiff IM 𝓘(ℝ, V) ∞ (map t u)
  immersion : ∀ t u x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (map t u) x)
  joint_smooth : ∀ t, 0 < t → t < threshold →
    ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry (map t)) (Metric.ball 0 radius ×ˢ univ)
  metric : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius → ∀ x,
    inducedMetric (I := IM) (map t u) x = inducedMetric (I := IM) F₀ x
  weight : Fin r → ℝ
  weight_pos : ∀ l, 0 < weight l
  distinct_on_overlap : ∀ l k, l ≠ k →
    (tsupport (waves l).cutoff ∩ tsupport (waves k).cutoff).Nonempty → weight l ≠ weight k
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  etaH : ℝ → ℝ
  etaV : ℝ → ℝ
  etaH_nonneg : ∀ t, 0 ≤ etaH t
  etaV_nonneg : ∀ t, 0 ≤ etaV t
  etaH_tendsto : Tendsto etaH (𝓝[>] 0) (𝓝 0)
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
  native_hessian_response : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    ∀ l b i x, x ∈ A.support i →
      ‖fderiv ℝ
          (fun v ↦ fderiv ℝ (fderiv ℝ (map t v ∘ (A.chart i).symm)) (A.chart i x))
          u (Pi.single (l, b) 1) -
        (t ^ ((44 : ℝ) / 5) * probeTrig b (weight l * (waves l).phase x /
          t ^ ((6 : ℝ) / 5))) •
          phaseRankOneHessian ((waves l).phase ∘ (A.chart i).symm)
            ((waves l).value ∘ (A.chart i).symm) (A.chart i x)‖ ≤
        t ^ ((44 : ℝ) / 5) * (etaH t + constant * ‖u‖)
  value_response : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
    ∀ l b x,
      ‖fderiv ℝ (fun v ↦ map t v x) u (Pi.single (l, b) 1) -
        (-(t ^ ((56 : ℝ) / 5)) * (weight l ^ 2)⁻¹ *
          probeTrig b (weight l * (waves l).phase x / t ^ ((6 : ℝ) / 5))) •
          (waves l).value x‖ ≤
        t ^ ((56 : ℝ) / 5) * (etaV t + constant * ‖u‖)
  reserve : ℝ
  reserve_lt_one : reserve < 1
  closeness_reserve : ∀ t, 0 < t → t < threshold →
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ u, ‖u‖ < radius → probeAtlasCj A 2 (map t u - F₀) ≤ ENNReal.ofReal b) ∧
      originalC2PolarConstant A hA hcompact hcover F₀ hF₀ hi₀ * b ≤ reserve

omit [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, E) M] in
/-- The former common-constant reserve is a sufficient convenience condition
for the genuine C²-budget reserve. The converse is not required: a tighter
actual closeness budget can keep the original domain when response constants
are enlarged. The numerical coefficient K can be the fixed original atlas
projection constant. -/
theorem nativeClosenessReserve_of_common_constant
    (F₀ : M → V) (A : BufferedAtlas M E) {r : ℕ}
    (F : ℝ → ProbeParameters r → M → V)
    (radius threshold constant K q : ℝ) (hconstant : 0 ≤ constant)
    (hclose : ∀ t, 0 < t → t < threshold → ∀ u, ‖u‖ < radius →
      probeAtlasCj A 2 (F t u - F₀) ≤ ENNReal.ofReal (constant * t ^ ((44 : ℝ) / 5)))
    (hreserve : ∀ t, 0 < t → t < threshold → K * (constant * t ^ ((44 : ℝ) / 5)) ≤ q) :
    ∀ t, 0 < t → t < threshold → ∃ b : ℝ, 0 ≤ b ∧
      (∀ u, ‖u‖ < radius → probeAtlasCj A 2 (F t u - F₀) ≤ ENNReal.ofReal b) ∧
      K * b ≤ q := by
  intro t ht htt
  exact ⟨constant * t ^ ((44 : ℝ) / 5),
    mul_nonneg hconstant (Real.rpow_nonneg ht.le _), hclose t ht htt, hreserve t ht htt⟩

namespace NativeProbeData

variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A}
    {hcompact : ∀ i, IsCompact (A.support i)}
    {hcover : ∀ x, ∃ i, x ∈ A.support i}
    {hi₀ : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x)}
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}

/-- The genuine projection reserve is derived from the original C² field. -/
theorem projection_gap (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < d.radius) (x : M) :
    ‖(normalSpace (I := IM) F₀ x).starProjection -
      (normalSpace (I := IM) (d.map t u) x).starProjection‖ ≤ d.reserve := by
  obtain ⟨b, hb, hclose, hreserve⟩ := d.closeness_reserve t ht htt
  exact (originalC2PolarConstant_projection_bound A hA hcompact hcover F₀ hF₀ hi₀
    (d.map t u) (d.slice_smooth t u) (d.metric t ht htt u hu)
    b hb (hclose u hu) x).trans hreserve

/-- Construct the original normal-bundle geometry, preserving the exact map,
parameter ball and threshold. No field of this geometry is assumed in d. -/
def geometry (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    ProbeGeometry (n := n) F₀ r :=
  probeGeometryOfActualImmersions F₀ hF₀ hi₀ d.map d.radius d.threshold
    d.radius_pos d.threshold_pos d.slice_smooth d.immersion d.joint_smooth d.metric
    (fun t ht htt u hu x ↦ (d.projection_gap t ht htt u hu x).trans_lt d.reserve_lt_one)

@[simp] theorem geometry_map (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    d.geometry.map = d.map := rfl

@[simp] theorem geometry_radius (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    d.geometry.radius = d.radius := rfl

@[simp] theorem geometry_threshold (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    d.geometry.threshold = d.threshold := rfl

@[simp] theorem geometry_normalIdentification
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) (t : ℝ)
    (u : ProbeParameters r) :
    d.geometry.normalIdentification t u =
      actualImmersionNormalIdentification F₀ (d.map t u) hi₀ (d.immersion t u) := rfl

end NativeProbeData
end GlobalEmbedding.NormalPolar
