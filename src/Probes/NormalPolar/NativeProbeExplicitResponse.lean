import NormalPolar.ExplicitResponseActualMap
import NormalPolar.NativeProbeData

/-!
# Explicit same-Q parameter response from original actual probe budgets

The reference coefficient is chosen before the reserve, actual family, wave
count, parameter radius and scale.  The only family-dependent coefficient is
the displayed elementary function of its original projection reserve.  The
same geometry, original parameter ball and atlas supports are retained.
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

/-- A fixed original-atlas first-jet coefficient. It is selected without an
actual family, projection reserve, wave count, radius or threshold. -/
def nativeReferenceResponseFactor
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x)) : ℝ :=
  (exists_uniform_reference_normal_response_factor A hA hcompact F₀ hF₀ hi₀).choose *
    probeAtlasDerivativeConstant n N 1 + 1

theorem nativeReferenceResponseFactor_pos
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x)) :
    0 < nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀ := by
  have hK := (exists_uniform_reference_normal_response_factor A hA hcompact F₀ hF₀ hi₀).choose_spec.1
  have hD := probeAtlasDerivativeConstant_nonneg n N 1
  unfold nativeReferenceResponseFactor
  positivity

theorem nativeReferenceResponseFactor_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
    (2 * ‖((probeAtlasFirstJet A F₀ i x).adjoint.comp
      (probeAtlasFirstJet A F₀ i x)).inverse‖ * ‖probeAtlasFirstJet A F₀ i x‖) *
        probeAtlasDerivativeConstant n N 1 ≤
      nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀ := by
  apply (mul_le_mul_of_nonneg_right
    ((exists_uniform_reference_normal_response_factor A hA hcompact F₀ hF₀ hi₀).choose_spec.2 i x hx)
    (probeAtlasDerivativeConstant_nonneg n N 1)).trans
  unfold nativeReferenceResponseFactor
  exact le_add_of_nonneg_right zero_le_one

namespace NativeProbeData

variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
    {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀}
    {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A}
    {hcompact : ∀ i, IsCompact (A.support i)}
    {hcover : ∀ x, ∃ i, x ∈ A.support i}
    {hi₀ : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F₀ x)}
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}

/-- The elementary reserve factor times one fixed reference coefficient.
Taking max with zero also covers an empty source without an extra assumption. -/
def explicitNormalResponseConstant
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) : ℝ :=
  normalPolarExplicitResponseConstant (max d.reserve 0) *
    nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀

theorem explicitNormalResponseConstant_nonneg
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves) :
    0 ≤ d.explicitNormalResponseConstant :=
  mul_nonneg (normalPolarExplicitResponseConstant_nonneg (le_max_right _ _))
    (nativeReferenceResponseFactor_pos A hA hcompact F₀ hF₀ hi₀).le

/-- An arbitrary true original C¹ response budget bounds this same Q, with
the explicit reserve coefficient and no Q-response hypothesis. -/
theorem normal_response_originalC1_explicit
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u a : ProbeParameters r) (hu : ‖u‖ < d.radius)
    (i : Fin A.count) (x : M) (hx : x ∈ A.support i)
    {b : ℝ} (hb : 0 ≤ b)
    (hbudget : probeAtlasCj A 1 (fun y ↦ fderiv ℝ (fun v ↦ d.map t v y) u a) ≤
      ENNReal.ofReal b) :
    ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (d.geometry.map t v)
      (d.geometry.normalIdentification t v) x) u a‖ ≤ d.explicitNormalResponseConstant * b := by
  let q := max d.reserve 0
  have hq : q < 1 := max_lt d.reserve_lt_one zero_lt_one
  have hq0 : 0 ≤ q := le_max_right _ _
  have hpoint := norm_fderiv_actualImmersionNormalIdentification_from_firstJet_le_explicit
    F₀ (d.map t) hF₀ (d.slice_smooth t) hi₀ (d.immersion t) A hA i x
    (hA.support_subset i hx) (U := Metric.ball 0 d.radius) Metric.isOpen_ball u a
    (by simpa using hu) q hq
    (d.geometry.atlas_firstJet_parameter_differentiable A hA i t ht htt u hu x
      (hA.support_subset i hx))
    (fun v hv ↦ d.metric t ht htt v (by simpa using hv) x)
    (fun v hv ↦ (d.projection_gap t ht htt v (by simpa using hv) x).trans (le_max_left _ _))
  rw [probeAtlasFirstJet_norm_eq_of_inducedMetric_eq A hA F₀ (d.map t u) hF₀
    (d.slice_smooth t u) i x (hA.support_subset i hx) (d.metric t ht htt u hu x)] at hpoint
  have hjet := d.geometry.atlas_firstJet_parameter_derivative_bound_of_originalC1
    A hA i t ht htt u a hu x hx hb hbudget
  apply hpoint.trans
  calc
    _ ≤ normalPolarExplicitResponseConstant q *
        ((2 * ‖((probeAtlasFirstJet A F₀ i x).adjoint.comp
          (probeAtlasFirstJet A F₀ i x)).inverse‖ * ‖probeAtlasFirstJet A F₀ i x‖) *
            (probeAtlasDerivativeConstant n N 1 * b)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hjet (by positivity))
        (normalPolarExplicitResponseConstant_nonneg hq0)
    _ ≤ normalPolarExplicitResponseConstant q *
        (nativeReferenceResponseFactor A hA hcompact F₀ hF₀ hi₀ * b) := by
      rw [← mul_assoc _ (probeAtlasDerivativeConstant n N 1) b]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (nativeReferenceResponseFactor_bound A hA hcompact F₀ hF₀ hi₀ i x hx) hb)
          (normalPolarExplicitResponseConstant_nonneg hq0)
    _ = d.explicitNormalResponseConstant * b := by
      simp only [explicitNormalResponseConstant, q, mul_assoc]

/-- The original actual C¹ field gives an explicit t^10 response at every
source point on the entire original parameter ball. -/
theorem normal_response_explicit
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u a : ProbeParameters r) (hu : ‖u‖ < d.radius) (x : M) :
    ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (d.geometry.map t v)
      (d.geometry.normalIdentification t v) x) u a‖ ≤
        (d.explicitNormalResponseConstant * d.constant) * t ^ (10 : ℕ) * ‖a‖ := by
  obtain ⟨i, hx⟩ := hcover x
  simpa only [mul_assoc] using d.normal_response_originalC1_explicit t ht htt u a hu i x hx
    (mul_nonneg (mul_nonneg d.constant_nonneg (pow_nonneg ht.le _)) (norm_nonneg a))
    (d.parameter_C1 t ht htt u hu a)

/-- The whole native derivative, with the same explicit constant. -/
theorem normal_derivative_explicit
    (d : NativeProbeData F₀ hF₀ A hA hcompact hcover hi₀ waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < d.radius) (x : M) :
    ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (d.geometry.map t v)
      (d.geometry.normalIdentification t v) x) u‖ ≤
        (d.explicitNormalResponseConstant * d.constant) * t ^ (10 : ℕ) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg d.explicitNormalResponseConstant_nonneg d.constant_nonneg)
      (pow_nonneg ht.le _))
  exact fun a ↦ d.normal_response_explicit t ht htt u a hu x

end NativeProbeData
end GlobalEmbedding.NormalPolar
