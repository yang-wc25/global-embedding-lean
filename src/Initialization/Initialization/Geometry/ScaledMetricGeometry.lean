import Initialization.Geometry.RescaledMetricIdentity
import Initialization.Geometry.CenteredRescaling
import Initialization.Assembly.PreparedCoframeBounds
import Initialization.Colored.SourceMetricCj

/-!
# Actual scaled metric coefficients, reference bounds and ellipticity

The coefficient operator below is proved to represent the native pullback of
the original metric T²g. Its all-order bounds and its positive ellipticity
constants are produced internally from the actual metric-normalized coframe and
fixed compact chart cores, before T or a scale net is chosen.
-/

open Set Metric Bundle Manifold IsManifold Topology Function
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

def preparedMetricOperator (p : Fin G.count) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  actualGramOperator (preparedCoframe G g f p y)

def scaledTargetMetricOperator {T : ℝ} (Q : ChartCutoffFamily G T)
    (p : Fin Q.count) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  preparedMetricOperator G g f (Q.parent p) (Q.center p + T⁻¹ • y)

/-- Exact bilinear identity with the actual native pullback of T²g. -/
theorem scaledTargetMetricOperator_inner {T : ℝ} (Q : ChartCutoffFamily G T)
    (hT : 1 ≤ T) (p : Fin Q.count) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ ((Q.boundedAtlas hT).chart p).target) (v w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (scaledTargetMetricOperator G g f Q p y v) w =
      T ^ 2 * g.inner (((Q.boundedAtlas hT).chart p).symm y)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          ((Q.boundedAtlas hT).chart p).symm y v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          ((Q.boundedAtlas hT).chart p).symm y w) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hcore := Q.scaledPoint_in_open_core hT p hy
  have htarget : T⁻¹ • y + Q.center p ∈ (G.chart (Q.parent p)).target := by
    rw [add_comm]
    exact G.buffered _ ((closedBall_subset_closedBall (by linarith [G.radius_pos (Q.parent p)]))
      (ball_subset_closedBall hcore))
  change inner ℝ ((preparedCoframe G g f (Q.parent p) (Q.center p + T⁻¹ • y)).adjoint
    (preparedCoframe G g f (Q.parent p) (Q.center p + T⁻¹ • y) v)) w = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hφ : (((Q.boundedAtlas hT).chart p).symm : EuclideanSpace ℝ (Fin n) → M) =
      ((rescaledChart (G.chart (Q.parent p)) (Q.center p) T hTpos.ne').symm :
        EuclideanSpace ℝ (Fin n) → M) := rfl
  rw [hφ]
  simpa only [preparedCoframe, add_comm] using
    rescaledChart_coframe_gram_eq_scaled_metric g f (G.chart (Q.parent p))
      (G.chart_smooth (Q.parent p)) (Q.center p) T hTpos.ne' htarget v w

theorem preparedMetricOperator_contDiffOn (p : Fin G.count) :
    ContDiffOn ℝ ∞ (preparedMetricOperator G g f p) (G.chart p).target := by
  have hθ := chartOrthonormalCoframe_contDiffOn g f (G.chart p) (G.chart_smooth p)
  let adj := ContinuousLinearMap.adjoint (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin n)) (F := EuclideanSpace ℝ (Fin n))
  exact (adj.contDiff.comp_contDiffOn hθ).clm_comp hθ

/-- Reference derivatives of the actual metric operator are generated on all
compact cores and aggregated over the fixed finite parent atlas. -/
theorem exists_preparedMetricOperator_derivative_bounds :
    ∃ B : ℕ → ℝ, (∀ j, 1 ≤ B j) ∧
      ∀ p j y, y ∈ closedBall (G.center p) (4 * G.radius p) →
        ‖iteratedFDeriv ℝ j (preparedMetricOperator G g f p) y‖ ≤ B j := by
  classical
  have each (p : Fin G.count) := exists_compact_smooth_derivative_bounds
    (isCompact_closedBall (G.center p) (4 * G.radius p)) (G.chart p).open_target (G.buffered p)
    (preparedMetricOperator G g f p) (preparedMetricOperator_contDiffOn G g f p)
  choose B hB hbound using each
  refine ⟨fun j ↦ 1 + ∑ p, B p j, ?_, ?_⟩
  · intro j
    have hs : 0 ≤ ∑ p, B p j := Finset.sum_nonneg (fun p _ ↦ hB p j)
    linarith
  · intro p j y hy
    have hs : B p j ≤ ∑ p, B p j :=
      Finset.single_le_sum (fun p _ ↦ hB p j) (Finset.mem_univ p)
    exact (hbound p j y hy).trans (by linarith)

/-- The actual T²g coefficient has full T⁻ʲ derivative scaling and hence
uniform reference bounds throughout each entire fixed target ball. -/
theorem exists_scaledTargetMetric_derivative_bounds :
    ∃ B : ℕ → ℝ, (∀ j, 1 ≤ B j) ∧
      ∀ T : ℝ, ∀ hT : 1 ≤ T, ∀ Q : ChartCutoffFamily G T,
        ∀ p j y, y ∈ ((Q.boundedAtlas hT).chart p).target →
          ‖iteratedFDeriv ℝ j (scaledTargetMetricOperator G g f Q p) y‖ ≤ B j * (T⁻¹)^j ∧
          ‖iteratedFDeriv ℝ j (scaledTargetMetricOperator G g f Q p) y‖ ≤ B j := by
  obtain ⟨B, hB, hbound⟩ := exists_preparedMetricOperator_derivative_bounds G g f
  refine ⟨B, hB, ?_⟩
  intro T hT Q p j y hy
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hcore : Q.center p + T⁻¹ • y ∈ closedBall (G.center (Q.parent p)) (4 * G.radius (Q.parent p)) :=
    (closedBall_subset_closedBall (by linarith [G.radius_pos (Q.parent p)]))
      (ball_subset_closedBall (Q.scaledPoint_in_open_core hT p hy))
  have hb : ‖iteratedFDeriv ℝ j (scaledTargetMetricOperator G g f Q p) y‖ ≤ B j * (T⁻¹)^j := by
    change ‖iteratedFDeriv ℝ j
      (fun z ↦ preparedMetricOperator G g f (Q.parent p) (Q.center p + T⁻¹ • z)) y‖ ≤ _
    rw [iteratedFDeriv_centered_rescaling _ _ hTpos.ne', norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hTpos.le) _)]
    exact (mul_le_mul_of_nonneg_left (hbound (Q.parent p) j _ hcore) (by positivity)).trans_eq (mul_comm _ _)
  exact ⟨hb, hb.trans ((mul_le_mul_of_nonneg_left
    (pow_le_one₀ (inv_nonneg.mpr hTpos.le) (inv_le_one_of_one_le₀ hT))
    (zero_le_one.trans (hB j))).trans_eq (mul_one _))⟩

/-- Positive ellipticity bounds for the actual T²g tensor, internally selected
before T and valid on every whole bounded-atlas target. No spectral budget or
positive lower bound is a new hypothesis. -/
theorem exists_scaledTargetMetric_ellipticity :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ T : ℝ, ∀ hT : 1 ≤ T, ∀ Q : ChartCutoffFamily G T,
        ∀ p y, y ∈ ((Q.boundedAtlas hT).chart p).target → ∀ v : EuclideanSpace ℝ (Fin n),
          lower * ‖v‖ ^ 2 ≤ inner ℝ (scaledTargetMetricOperator G g f Q p y v) v ∧
          inner ℝ (scaledTargetMetricOperator G g f Q p y v) v ≤ upper * ‖v‖ ^ 2 := by
  obtain ⟨B, L, hB, hL, hbound, hinverse⟩ := exists_preparedCoframe_uniform_bounds G g f
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hBp : 0 < B 0 := zero_lt_one.trans_le (hB 0)
  refine ⟨(L ^ 2)⁻¹, (B 0) ^ 2, inv_pos.mpr (sq_pos_of_pos hLp), sq_pos_of_pos hBp, ?_⟩
  intro T hT Q p y hy v
  let z := Q.center p + T⁻¹ • y
  let θ := preparedCoframe G g f (Q.parent p) z
  have hz : z ∈ closedBall (G.center (Q.parent p)) (4 * G.radius (Q.parent p)) :=
    (closedBall_subset_closedBall (by linarith [G.radius_pos (Q.parent p)]))
      (ball_subset_closedBall (Q.scaledPoint_in_open_core hT p hy))
  have hθ : ‖θ‖ ≤ B 0 := by
    simpa only [norm_iteratedFDeriv_zero] using hbound 0 (Q.parent p) z hz
  have hupper : ‖θ v‖ ≤ B 0 * ‖v‖ :=
    (θ.le_opNorm v).trans (mul_le_mul_of_nonneg_right hθ (norm_nonneg _))
  have hlower : ‖v‖ ≤ L * ‖θ v‖ :=
    chartOrthonormalCoframe_ellipticity g f (G.chart (Q.parent p)) (G.chart_smooth _)
      z (G.buffered _ hz) L (hinverse (Q.parent p) z hz) v
  have hquad : inner ℝ (scaledTargetMetricOperator G g f Q p y v) v = ‖θ v‖ ^ 2 := by
    change inner ℝ (θ.adjoint (θ v)) v = _
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  rw [hquad]
  constructor
  · have hs : ‖v‖ ^ 2 ≤ L ^ 2 * ‖θ v‖ ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg v) hlower 2
    calc
      (L ^ 2)⁻¹ * ‖v‖ ^ 2 = ‖v‖ ^ 2 / (L ^ 2) := by ring
      _ ≤ ‖θ v‖ ^ 2 := (div_le_iff₀ (sq_pos_of_pos hLp)).mpr (by simpa only [mul_comm] using hs)
  · simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (θ v)) hupper 2

end GlobalEmbedding.Initialization
