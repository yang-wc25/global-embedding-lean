import Initialization.Assembly.PreparedCoframeBounds
import Initialization.Geometry.ScaledBufferedAtlas
import Initialization.Geometry.CenteredRescaling

/-!
# Actual metric-generated affine phases and their freezing errors

The coefficient field is the actual positive-root normalized coframe pulled
back by the actual parent chart. All bounds are produced from the original
metric and full tangent frame; no coframe smoothness, coordinate bound or
freezing estimate is assumed as an additional input.
-/

open Set Metric Filter Bundle Manifold IsManifold Topology
open scoped ContDiff Manifold

noncomputable section
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

/-- The actual vector of local affine phases. The real oscillation parameter
T is deliberately absent: it belongs only in the later exponential. -/
def ChartCutoffFamily.frozenVectorPhase {K : ℝ} (F : ChartCutoffFamily G K)
    (i : Fin F.count) (x : M) : EuclideanSpace ℝ (Fin n) :=
  preparedCoframe G g f (F.parent i) (F.center i)
    (G.chart (F.parent i) x - F.center i)

theorem ChartCutoffFamily.frozenVectorPhase_contMDiffOn {K : ℝ}
    (F : ChartCutoffFamily G K) (i : Fin F.count) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (F.frozenVectorPhase G g f i)
      (G.chart (F.parent i)).source := by
  exact (preparedCoframe G g f (F.parent i) (F.center i)).contDiff.contMDiff.comp_contMDiffOn
    ((contMDiffOn_of_mem_maximalAtlas (G.chart_smooth (F.parent i))).sub contMDiffOn_const)

/-- The true own-chart representative equals the affine phase on a genuine
neighborhood; arbitrary off-domain inverse-chart values are irrelevant. -/
theorem ChartCutoffFamily.frozenVectorPhase_ownChart_eventuallyEq {K : ℝ}
    (F : ChartCutoffFamily G K) (i : Fin F.count)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (G.chart (F.parent i)).target) :
    (F.frozenVectorPhase G g f i ∘ (G.chart (F.parent i)).symm) =ᶠ[𝓝 y]
      frozenCoframePhase (preparedCoframe G g f (F.parent i)) (F.center i) := by
  filter_upwards [(G.chart (F.parent i)).open_target.mem_nhds hy] with z hz
  change preparedCoframe G g f (F.parent i) (F.center i)
    (G.chart (F.parent i) ((G.chart (F.parent i)).symm z) - F.center i) = _
  rw [(G.chart (F.parent i)).right_inv hz]
  rfl

/-- Exact derivative of the actual local phase in its parent coordinates. -/
theorem ChartCutoffFamily.frozenVectorPhase_ownChart_fderiv {K : ℝ}
    (F : ChartCutoffFamily G K) (i : Fin F.count)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (G.chart (F.parent i)).target) :
    fderiv ℝ (F.frozenVectorPhase G g f i ∘ (G.chart (F.parent i)).symm) y =
      preparedCoframe G g f (F.parent i) (F.center i) := by
  rw [(F.frozenVectorPhase_ownChart_eventuallyEq G g f i hy).fderiv_eq]
  exact frozenCoframePhase_fderiv _ _ _

/-- Actual coframe freezing with constants fixed before every K,T and every
net choice. The zeroth error is O(K⁻¹) on the actual enlarged supports; each
positive rescaled derivative of the same frozen error is O(T⁻¹). -/
theorem exists_actual_frozenCoframe_bounds :
    ∃ (C : ℝ) (B : ℕ → ℝ), 0 < C ∧ (∀ j, 1 ≤ B j) ∧
      (∀ K : ℝ, ∀ hK : 1 ≤ K, ∀ F : ChartCutoffFamily G K,
        ∀ i x, x ∈ F.enlargedSupport i →
        ‖fderiv ℝ (F.frozenVectorPhase G g f i ∘ (G.chart (F.parent i)).symm)
            (G.chart (F.parent i) x) -
          preparedCoframe G g f (F.parent i) (G.chart (F.parent i) x)‖ ≤ C / K) ∧
      (∀ i (p q : EuclideanSpace ℝ (Fin n)) (T : ℝ), 1 ≤ T →
        ∀ j : ℕ, 1 ≤ j → ∀ y,
          q + T⁻¹ • y ∈ closedBall (G.center i) (4 * G.radius i) →
        ‖iteratedFDeriv ℝ j (fun z ↦ preparedCoframe G g f i p -
          preparedCoframe G g f i (q + T⁻¹ • z)) y‖ ≤ B j / T) := by
  obtain ⟨B, L, hB, _hL, hbound, _hinverse⟩ := exists_preparedCoframe_uniform_bounds G g f
  refine ⟨B 1 * G.scaleRadius, B, mul_pos (zero_lt_one.trans_le (hB 1)) G.scaleRadius_pos,
    hB, ?_, ?_⟩
  · intro K hK F i x hx
    rw [F.frozenVectorPhase_ownChart_fderiv G g f i
      ((G.chart (F.parent i)).map_source hx.1), norm_sub_rev]
    let θ := preparedCoframe G g f (F.parent i)
    let s := closedBall (G.center (F.parent i)) (4 * G.radius (F.parent i))
    have hθ : ContDiffOn ℝ ∞ θ (G.chart (F.parent i)).target :=
      chartOrthonormalCoframe_contDiffOn g f _ (G.chart_smooth (F.parent i))
    have hd (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ s) : DifferentiableAt ℝ θ z :=
      (hθ.contDiffAt ((G.chart (F.parent i)).open_target.mem_nhds
        (G.buffered (F.parent i) hz))).differentiableAt (by simp)
    have hb (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ s) : ‖fderiv ℝ θ z‖ ≤ B 1 := by
      simpa only [norm_iteratedFDeriv_one] using hbound 1 (F.parent i) z hz
    have hp : F.center i ∈ s :=
      (closedBall_subset_closedBall (by linarith [G.radius_pos (F.parent i)])) (F.center_core i)
    have hy : G.chart (F.parent i) x ∈ s :=
      (closedBall_subset_closedBall (by linarith [G.radius_pos (F.parent i)]))
        (F.enlargedSupport_in_core hK i hx)
    have hconv : Convex ℝ s := convex_closedBall _ _
    have he := hconv.norm_image_sub_le_of_norm_fderiv_le hd hb hp hy
    have hdist : ‖G.chart (F.parent i) x - F.center i‖ ≤ G.scaleRadius / K := by
      have hsmall : dist (G.chart (F.parent i) x) (F.center i) ≤ G.scaleRadius / (4 * K) := hx.2
      rw [← dist_eq_norm]
      apply hsmall.trans
      apply div_le_div_of_nonneg_left G.scaleRadius_pos.le (zero_lt_one.trans_le hK)
      linarith
    exact he.trans ((mul_le_mul_of_nonneg_left hdist (zero_le_one.trans (hB 1))).trans_eq (by ring))
  · intro i p q T hT j hj y hy
    have hTpos : 0 < T := zero_lt_one.trans_le hT
    have hθ : ContDiffAt ℝ j (preparedCoframe G g f i) (q + T⁻¹ • y) :=
      ((chartOrthonormalCoframe_contDiffOn g f _ (G.chart_smooth i)).contDiffAt
        ((G.chart i).open_target.mem_nhds (G.buffered i hy))).of_le (by simp)
    rw [iteratedFDeriv_frozen_error_rescaled _ p q hTpos.ne' (by omega) y hθ,
      norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hTpos.le) _)]
    calc
      (T⁻¹) ^ j * ‖iteratedFDeriv ℝ j (preparedCoframe G g f i) (q + T⁻¹ • y)‖ ≤
          (T⁻¹) ^ j * B j := mul_le_mul_of_nonneg_left (hbound j i _ hy) (by positivity)
      _ ≤ T⁻¹ * B j := mul_le_mul_of_nonneg_right
        (pow_le_of_le_one (inv_nonneg.mpr hTpos.le) (inv_le_one_of_one_le₀ hT) (by omega))
        (zero_le_one.trans (hB j))
      _ = B j / T := by ring

end GlobalEmbedding.Initialization
