import Main.GeneralFullResponse
import Main.GeneralExactProbeFamily

/-!
# Original GeneralExactProbeFamily from actual native map and jet data

The construction fills the normal identification, its joint smoothness and
the complete identified second-form response from proved geometric results.
It preserves the supplied actual map, original parameter domain and weights.
Only the common quantitative constant is enlarged. The same-Q gap is derived
from the same input's original C² budget and attached to this exact output.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Upgrade GlobalEmbedding.NormalPolar SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

namespace GeneralNativeProbeData

variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A}
    {hcompact : ∀ i, IsCompact (A.support i)}
    {hcover : ∀ x, ∃ i, x ∈ A.support i}
    {hi₀ : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x)}
    {r : ℕ} {waves : Fin r → OpenSupportedLegalWave F₀ hF₀}

/-- The linear coefficient obtained from the proved full response bound. -/
def responseConstant (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) : ℝ :=
  d.exists_secondForm_response.choose

theorem responseConstant_nonneg
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    0 ≤ d.responseConstant := d.exists_secondForm_response.choose_spec.1

/-- The vanishing modulus obtained from native Hessian response, the derived
same-Q gap and the proved actual Q derivative bound. -/
def responseModulus (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) : ℝ → ℝ :=
  d.exists_secondForm_response.choose_spec.2.choose

theorem responseModulus_nonneg
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) (t : ℝ) :
    0 ≤ d.responseModulus t := d.exists_secondForm_response.choose_spec.2.choose_spec.1 t

theorem responseModulus_tendsto
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    Tendsto d.responseModulus (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  d.exists_secondForm_response.choose_spec.2.choose_spec.2.1

theorem secondForm_response
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < d.radius)
    (l : Fin r) (b : Bool) (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
    ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i x)
        (identifiedTrueSecondForm (n := n) F₀ (d.geometry.map t v)
          (d.geometry.slice_smooth t v) (d.geometry.normalIdentification t v) x))
        u (Pi.single (l, b) 1) -
      (t ^ ((44 : ℝ) / 5) * probeTrig b (d.weight l * (waves l).phase x /
        t ^ ((6 : ℝ) / 5))) •
        probeTensorInFrame (probeAtlasFrame A i x) ((waves l).tensor x)‖ ≤
      t ^ ((44 : ℝ) / 5) * (d.responseModulus t + d.responseConstant * ‖u‖) :=
  d.exists_secondForm_response.choose_spec.2.choose_spec.2.2 t ht htt u hu l b i x hx

/-- The original full record for the same actual mapping family. The normal
fields and full identified-form response are constructed, not assumed.
The enlarged constant changes none of map, Q, radius, threshold or weights. -/
def toGeneralExactProbeFamily
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    GeneralExactProbeFamily F₀ hF₀ A waves where
  toProbeGeometry := d.geometry
  weight := d.weight
  weight_pos := d.weight_pos
  distinct_on_overlap := d.distinct_on_overlap
  constant := max d.constant d.responseConstant
  constant_nonneg := d.constant_nonneg.trans (le_max_left _ _)
  etaB := d.responseModulus
  etaV := d.etaV
  etaB_nonneg := d.responseModulus_nonneg
  etaV_nonneg := d.etaV_nonneg
  etaB_tendsto := d.responseModulus_tendsto
  etaV_tendsto := d.etaV_tendsto
  closeness := by
    intro t ht htt u hu
    apply (d.closeness t ht htt u hu).trans
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg ht.le _))
  spatial_C3 := by
    intro t ht htt u hu
    exact (d.spatial_C3 t ht htt u hu).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  parameter_C1 := by
    intro t ht htt u hu a
    apply (d.parameter_C1 t ht htt u hu a).trans
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg ht.le _)) (norm_nonneg a))
  parameter_C2 := by
    intro t ht htt u hu a
    apply (d.parameter_C2 t ht htt u hu a).trans
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht.le _)) (norm_nonneg a))
  secondForm_response := by
    intro t ht htt u hu l b i x hx
    apply (d.secondForm_response t ht htt u hu l b i x hx).trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg u))
  value_response := by
    intro t ht htt u hu l b x
    apply (d.value_response t ht htt u hu l b x).trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg u))

@[simp] theorem toGeneralExactProbeFamily_geometry
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    d.toGeneralExactProbeFamily.toProbeGeometry = d.geometry := rfl

@[simp] theorem toGeneralExactProbeFamily_map
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    d.toGeneralExactProbeFamily.map = d.map := rfl

@[simp] theorem toGeneralExactProbeFamily_radius
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    d.toGeneralExactProbeFamily.radius = d.radius := rfl

@[simp] theorem toGeneralExactProbeFamily_threshold
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    d.toGeneralExactProbeFamily.threshold = d.threshold := rfl

@[simp] theorem toGeneralExactProbeFamily_weight
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    d.toGeneralExactProbeFamily.weight = d.weight := rfl

@[simp] theorem toGeneralExactProbeFamily_normalIdentification
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    d.toGeneralExactProbeFamily.normalIdentification = d.geometry.normalIdentification := rfl

/-- The full arbitrary-cutoff output and its actual same-identification gap.
No extra wave regularity, repaired family or second-form response is assumed. -/
theorem exists_generalExactProbeFamily_with_sameQ_gap
    (d : GeneralNativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    ∃ probe : GeneralExactProbeFamily F₀ hF₀ A waves,
      probe.toProbeGeometry = d.geometry ∧ probe.weight = d.weight ∧
      ∃ gap : ℝ → ℝ, (∀ t, 0 ≤ gap t) ∧
        Tendsto gap (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        ∀ t, 0 < t → t < probe.threshold → ∀ u, ‖u‖ < probe.radius →
          ∀ i x, x ∈ A.support i →
            ‖normalIdentificationOperator (n := n) F₀ (probe.map t u)
              (probe.normalIdentification t u) x -
              (normalSpace (I := IM) F₀ x).starProjection‖ ≤ gap t :=
  ⟨d.toGeneralExactProbeFamily, rfl, rfl, d.normalGap,
    d.normalGap_nonneg, d.normalGap_tendsto, d.normalGap_bound⟩

end GeneralNativeProbeData
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.GeneralNativeProbeData.toGeneralExactProbeFamily
#print axioms GlobalEmbedding.Continuation.GeneralNativeProbeData.exists_generalExactProbeFamily_with_sameQ_gap
