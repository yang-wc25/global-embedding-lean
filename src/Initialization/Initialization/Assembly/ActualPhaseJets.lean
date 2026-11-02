import Initialization.Assembly.ChartCoframeNaturality
import Initialization.Geometry.ActualCoframeFreezing
import Initialization.Geometry.CoordinateExtensionJets

/-!
# Actual cross-chart phase jets

The phase is the literal affine phase of the actual metric coframe, pulled back
through an arbitrary actual reference chart and centered inverse dilation.
The bounds below are produced from fixed coordinate extensions and compact
coframe bounds. They precede K,T, net choices, and active patches.
-/

noncomputable section
open Bundle Manifold Set Metric Filter IsManifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)

def actualPhaseCoordinate {K : ℝ} (F : ChartCutoffFamily G K)
    (p : Fin G.count) (q : EuclideanSpace ℝ (Fin n)) (T : ℝ)
    (i : Fin F.count) (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  F.frozenVectorPhase G g f i ((G.chart p).symm (q + T⁻¹ • y))

def actualReferenceCoframe (p : Fin G.count) (q : EuclideanSpace ℝ (Fin n))
    (T : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  preparedCoframe G g f p (q + T⁻¹ • y)

def actualPhaseRateError {K : ℝ} (F : ChartCutoffFamily G K)
    (p : Fin G.count) (q : EuclideanSpace ℝ (Fin n)) (T : ℝ)
    (i : Fin F.count) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  T • fderiv ℝ (actualPhaseCoordinate G g f F p q T i) y -
    actualReferenceCoframe G g f p q T y

theorem ChartCutoffFamily.frozenVectorPhase_eventuallyEq_extension
    {K : ℝ} (F : ChartCutoffFamily G K) (hK : 1 ≤ K)
    (ext : Fin G.count → M → EuclideanSpace ℝ (Fin n))
    (hext : ∀ i x, x ∈ (G.chart i).source →
      G.chart i x ∈ closedBall (G.center i) (2 * G.radius i) → ext i x = G.chart i x)
    (i : Fin F.count) {x : M} (hx : x ∈ F.enlargedSupport i) :
    F.frozenVectorPhase G g f i =ᶠ[𝓝 x]
      (fun z ↦ preparedCoframe G g f (F.parent i) (F.center i)
        (ext (F.parent i) z - F.center i)) := by
  have he := prepared_coordinate_extension_eventuallyEq G ext hext (F.parent i) hx.1
    (F.enlargedSupport_in_open_core hK i hx)
  filter_upwards [he] with z hz
  change preparedCoframe G g f (F.parent i) (F.center i)
    (G.chart (F.parent i) z - F.center i) = _
  rw [hz]

/-- All positive-order actual unscaled phase derivatives are bounded on every
reference core, uniformly over the actual K-net and its centers. -/
theorem exists_actual_frozenPhase_unscaled_bounds [CompactSpace M] :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ K : ℝ, ∀ hK : 1 ≤ K, ∀ F : ChartCutoffFamily G K,
      ∀ p i j, 1 ≤ j → ∀ y,
        y ∈ closedBall (G.center p) (2 * G.radius p) →
        (G.chart p).symm y ∈ F.enlargedSupport i →
        ‖iteratedFDeriv ℝ j
          (F.frozenVectorPhase G g f i ∘ (G.chart p).symm) y‖ ≤ B j := by
  obtain ⟨ext, A, hA, hext, heq, hjets⟩ := exists_prepared_coordinate_extension_jets G
  obtain ⟨B, L, hB, _hL, hcoef, _hinverse⟩ := exists_preparedCoframe_uniform_bounds G g f
  refine ⟨fun j ↦ B 0 * A j, fun j ↦ mul_nonneg (zero_le_one.trans (hB 0)) (hA j), ?_⟩
  intro K hK F p i j hj y hy hx
  have hyt : y ∈ (G.chart p).target :=
    G.buffered p ((closedBall_subset_closedBall (by linarith [G.radius_pos p])) hy)
  have hgerm := (F.frozenVectorPhase_eventuallyEq_extension G g f hK ext heq i hx).comp_tendsto
    ((G.chart p).symm.continuousAt hyt)
  rw [(hgerm.iteratedFDeriv ℝ j).eq_of_nhds]
  let a := preparedCoframe G g f (F.parent i) (F.center i)
  let ψ := ext (F.parent i) ∘ (G.chart p).symm
  have hψ : ContDiffAt ℝ ∞ ψ y :=
    (((hext (F.parent i)).comp_contMDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas (G.chart_smooth p))).contDiffOn).contDiffAt
        ((G.chart p).open_target.mem_nhds hyt)
  have ha : ‖a‖ ≤ B 0 := by
    simpa only [norm_iteratedFDeriv_zero] using
      hcoef 0 (F.parent i) (F.center i)
        ((closedBall_subset_closedBall (by linarith [G.radius_pos (F.parent i)])) (F.center_core i))
  change ‖iteratedFDeriv ℝ j (a ∘ (fun z ↦ ψ z - F.center i)) y‖ ≤ _
  calc
    _ ≤ ‖a‖ * ‖iteratedFDeriv ℝ j (fun z ↦ ψ z - F.center i) y‖ :=
      a.norm_iteratedFDeriv_comp_left (hψ.sub contDiffAt_const) (by simp)
    _ = ‖a‖ * ‖iteratedFDeriv ℝ j ψ y‖ := by
      rw [iteratedFDeriv_sub_fixed_center ψ (F.center i) (by omega) y (hψ.of_le (by simp))]
    _ ≤ B 0 * A j := mul_le_mul ha (hjets p (F.parent i) j y hy)
      (norm_nonneg _) (zero_le_one.trans (hB 0))

/-- Every actual cross-chart phase has a bounded frequency-weighted jet on
the genuine reference cores, for every real T≥1. The stronger T⁻ʲ estimate is
retained for differentiating its actual rate discrepancy. -/
theorem exists_actual_frozenPhase_rescaled_bounds [CompactSpace M] :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (K T : ℝ), ∀ hK : 1 ≤ K, ∀ hT : 1 ≤ T, ∀ F : ChartCutoffFamily G K,
      ∀ (p : Fin G.count) (q : EuclideanSpace ℝ (Fin n)) i j, 1 ≤ j → ∀ y,
        q + T⁻¹ • y ∈ closedBall (G.center p) (2 * G.radius p) →
        (G.chart p).symm (q + T⁻¹ • y) ∈ F.enlargedSupport i →
        ‖iteratedFDeriv ℝ j (actualPhaseCoordinate G g f F p q T i) y‖ ≤ B j * (T⁻¹)^j ∧
        |T| * ‖iteratedFDeriv ℝ j (actualPhaseCoordinate G g f F p q T i) y‖ ≤ B j := by
  obtain ⟨B, hB, hb⟩ := exists_actual_frozenPhase_unscaled_bounds G g f
  refine ⟨B, hB, ?_⟩
  intro K T hK hT F p q i j hj y hy hx
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hjet : ‖iteratedFDeriv ℝ j (actualPhaseCoordinate G g f F p q T i) y‖ ≤
      B j * (T⁻¹)^j := by
    change ‖iteratedFDeriv ℝ j
      (fun z ↦ (F.frozenVectorPhase G g f i ∘ (G.chart p).symm) (q + T⁻¹ • z)) y‖ ≤ _
    rw [iteratedFDeriv_centered_rescaling _ q hTpos.ne', norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hTpos.le) _)]
    exact (mul_le_mul_of_nonneg_left (hb K hK F p i j hj _ hy hx)
      (by positivity)).trans_eq (mul_comm _ _)
  refine ⟨hjet, ?_⟩
  rw [abs_of_pos hTpos]
  calc
    _ ≤ T * (B j * (T⁻¹)^j) := mul_le_mul_of_nonneg_left hjet hTpos.le
    _ ≤ T * (B j * T⁻¹) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (pow_le_of_le_one (inv_nonneg.mpr hTpos.le) (inv_le_one_of_one_le₀ hT) (by omega))
        (hB j)) hTpos.le
    _ = B j := by field_simp

end GlobalEmbedding.Initialization
