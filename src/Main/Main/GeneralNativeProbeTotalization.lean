import NormalPolar.ActualFamilyTotalization
import Main.GeneralNativeProbeConstruction

/-!
# Full native probes from actual data only on the admitted domain

This input drops the former total slice smoothness and total immersion
requirements. Joint smoothness and the real metric on the original admitted
domain suffice. The explicit reference extension supplies total smooth
slices and total immersion; local equality transports every actual native
response and original atlas estimate with exactly the same constants.

The final actual family on the original domain is still an upstream analytic
input. This does not construct its repair limit or assert an original target.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- Actual native analytic data on the original scale interval and parameter
ball. No smoothness or immersion is requested for unprescribed outside slices,
and no field of the constructed normal identification is supplied. -/
structure GeneralNativeProbeDomainData
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    {r : ℕ} (waves : Fin r → OpenSupportedLegalWave F₀ hF₀) where
  radius : ℝ
  radius_pos : 0 < radius
  threshold : ℝ
  threshold_pos : 0 < threshold
  map : ℝ → ProbeParameters r → M → V
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

namespace GeneralNativeProbeDomainData

variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A}
    {hcompact : ∀ i, IsCompact (A.support i)}
    {hcover : ∀ x, ∃ i, x ∈ A.support i}
    {hi₀ : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x)}
    {r : ℕ} {waves : Fin r → OpenSupportedLegalWave F₀ hF₀}

/-- The total map chooses only outside values. -/
def totalMap (d : GeneralNativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    ℝ → ProbeParameters r → M → V :=
  actualFamilyTotalization F₀ d.map d.radius d.threshold

theorem totalMap_eq (d : GeneralNativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < d.radius) : d.totalMap t u = d.map t u :=
  actualFamilyTotalization_eq F₀ d.map d.radius d.threshold t ht htt u hu

/-- Fill the existing native data with the explicit reference extension.
All original norms and responses are transported by actual function equality
or equality on a parameter neighborhood; no numerical constant changes. -/
def toGeneralNativeProbeData
    (d : GeneralNativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves where
  radius := d.radius
  radius_pos := d.radius_pos
  threshold := d.threshold
  threshold_pos := d.threshold_pos
  map := d.totalMap
  slice_smooth := actualFamilyTotalization_slice_smooth F₀ hF₀ d.map d.radius d.threshold d.joint_smooth
  immersion := actualFamilyTotalization_immersion F₀ hi₀ d.map d.radius d.threshold d.metric
  joint_smooth := actualFamilyTotalization_joint_smooth F₀ d.map d.radius d.threshold d.joint_smooth
  metric := fun t _ _ u _ ↦
    actualFamilyTotalization_metric F₀ d.map d.radius d.threshold d.metric t u
  weight := d.weight
  weight_pos := d.weight_pos
  distinct_on_overlap := d.distinct_on_overlap
  constant := d.constant
  constant_nonneg := d.constant_nonneg
  etaH := d.etaH
  etaV := d.etaV
  etaH_nonneg := d.etaH_nonneg
  etaV_nonneg := d.etaV_nonneg
  etaH_tendsto := d.etaH_tendsto
  etaV_tendsto := d.etaV_tendsto
  closeness := by
    intro t ht htt u hu
    rw [d.totalMap_eq t ht htt u hu]
    exact d.closeness t ht htt u hu
  spatial_C3 := by
    intro t ht htt u hu
    rw [d.totalMap_eq t ht htt u hu]
    exact d.spatial_C3 t ht htt u hu
  parameter_C1 := by
    intro t ht htt u hu v
    rw [show (fun x ↦ fderiv ℝ (fun w ↦ d.totalMap t w x) u v) =
      (fun x ↦ fderiv ℝ (fun w ↦ d.map t w x) u v) from
      actualFamilyTotalization_parameterDerivative F₀ d.map d.radius d.threshold t ht htt u hu v]
    exact d.parameter_C1 t ht htt u hu v
  parameter_C2 := by
    intro t ht htt u hu v
    rw [show (fun x ↦ fderiv ℝ (fun w ↦ d.totalMap t w x) u v) =
      (fun x ↦ fderiv ℝ (fun w ↦ d.map t w x) u v) from
      actualFamilyTotalization_parameterDerivative F₀ d.map d.radius d.threshold t ht htt u hu v]
    exact d.parameter_C2 t ht htt u hu v
  native_hessian_response := by
    intro t ht htt u hu l b i x hx
    have heq := actualFamilyTotalization_fderiv_comp F₀ d.map d.radius d.threshold t ht htt u hu
      (fun H : M → V ↦ fderiv ℝ (fderiv ℝ (H ∘ (A.chart i).symm)) (A.chart i x))
    change fderiv ℝ (fun v ↦ fderiv ℝ (fderiv ℝ (d.totalMap t v ∘ (A.chart i).symm))
      (A.chart i x)) u = _ at heq
    rw [heq]
    exact d.native_hessian_response t ht htt u hu l b i x hx
  value_response := by
    intro t ht htt u hu l b x
    have heq := actualFamilyTotalization_fderiv_comp F₀ d.map d.radius d.threshold t ht htt u hu
      (fun H : M → V ↦ H x)
    change fderiv ℝ (fun v ↦ d.totalMap t v x) u = _ at heq
    rw [heq]
    exact d.value_response t ht htt u hu l b x
  reserve := d.reserve
  reserve_lt_one := d.reserve_lt_one
  closeness_reserve := by
    intro t ht htt
    obtain ⟨b, hb, hc, hsmall⟩ := d.closeness_reserve t ht htt
    refine ⟨b, hb, ?_, hsmall⟩
    intro u hu
    rw [d.totalMap_eq t ht htt u hu]
    exact hc u hu

/-- The same full original record is constructed using the proven normal
polar fields and identified-form response. -/
def toGeneralExactProbeFamily [T2Space M]
    (d : GeneralNativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    GeneralExactProbeFamily F₀ hF₀ A waves := d.toGeneralNativeProbeData.toGeneralExactProbeFamily

/-- Preserve all actual admitted slices and the original geometric domain.
Only the unprescribed outside total-map values have been chosen. -/
theorem toGeneralExactProbeFamily_preserves_admitted [T2Space M]
    (d : GeneralNativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    d.toGeneralExactProbeFamily.radius = d.radius ∧
    d.toGeneralExactProbeFamily.threshold = d.threshold ∧
    d.toGeneralExactProbeFamily.weight = d.weight ∧
    (∀ t, 0 < t → t < d.threshold → ∀ u, ‖u‖ < d.radius →
      d.toGeneralExactProbeFamily.map t u = d.map t u) :=
  ⟨rfl, rfl, rfl, fun t ht htt u hu ↦ d.totalMap_eq t ht htt u hu⟩

/-- Native parameter-response fields are literally unchanged on the open
ball, so every original source norm sees the same function. -/
theorem toGeneralExactProbeFamily_parameterDerivative [T2Space M]
    (d : GeneralNativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < d.radius) (v : ProbeParameters r) :
    (fun x ↦ fderiv ℝ (fun w ↦ d.toGeneralExactProbeFamily.map t w x) u v) =
      (fun x ↦ fderiv ℝ (fun w ↦ d.map t w x) u v) :=
  actualFamilyTotalization_parameterDerivative F₀ d.map d.radius d.threshold t ht htt u hu v

/-- The admitted Q is exactly the explicit polar expression in the actual
unextended final map's projections. Choosing outside values cannot choose a
different gauge on the original domain. -/
theorem toGeneralExactProbeFamily_normalOperator_eq [T2Space M]
    (d : GeneralNativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < d.radius) (x : M) :
    normalIdentificationOperator (n := n) F₀ (d.toGeneralExactProbeFamily.map t u)
      (d.toGeneralExactProbeFamily.normalIdentification t u) x =
      actualPolarOperator (normalSpace (I := IM) F₀ x).starProjection
        (normalSpace (I := IM) (d.map t u) x).starProjection := by
  change normalIdentificationOperator (n := n) F₀ (d.totalMap t u)
    (actualImmersionNormalIdentification F₀ (d.totalMap t u) hi₀
      (d.toGeneralNativeProbeData.immersion t u)) x = _
  rw [actualImmersionNormalIdentification_operator F₀ (d.totalMap t u) hi₀
    (d.toGeneralNativeProbeData.immersion t u) x
    ((d.toGeneralNativeProbeData.projection_gap t ht htt u hu x).trans_lt d.reserve_lt_one)]
  rw [d.totalMap_eq t ht htt u hu]

/-- The genuine parameter derivative of this Q is the derivative of the
explicit polar expression of the actual raw family on the original ball.
This uses neighborhood equality, not merely equality at the evaluation point. -/
theorem toGeneralExactProbeFamily_normalOperator_fderiv_eq [T2Space M]
    (d : GeneralNativeProbeDomainData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < d.radius) (x : M) :
    fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀
      (d.toGeneralExactProbeFamily.map t v) (d.toGeneralExactProbeFamily.normalIdentification t v) x) u =
    fderiv ℝ (fun v ↦ actualPolarOperator
      (normalSpace (I := IM) F₀ x).starProjection
      (normalSpace (I := IM) (d.map t v) x).starProjection) u := by
  apply Filter.EventuallyEq.fderiv_eq
  have hball : Metric.ball (0 : ProbeParameters r) d.radius ∈ 𝓝 u :=
    Metric.isOpen_ball.mem_nhds (by simpa using hu)
  filter_upwards [hball] with v hv
  exact d.toGeneralExactProbeFamily_normalOperator_eq t ht htt v (by simpa using hv) x

end GeneralNativeProbeDomainData
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.GeneralNativeProbeDomainData.toGeneralExactProbeFamily
#print axioms GlobalEmbedding.Continuation.GeneralNativeProbeDomainData.toGeneralExactProbeFamily_normalOperator_fderiv_eq
