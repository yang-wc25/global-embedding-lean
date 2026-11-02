import Initialization.Geometry.BoundedScaledAtlas
import Initialization.Geometry.CenteredRescaling
import Initialization.Assembly.ActualPhaseJets

/-!
# Actual invertible coframe coefficients on every bounded rescaled chart

This supplies the actual coefficient equivalence used by the selector phase
transport. Its forward map is exactly the rate field of the same original
metric-normalized coframe. Uniform forward, inverse and all-order budgets are
constructed before T, with full T⁻ʲ gains and no additional geometric inputs.
-/

open Set Metric Bundle Manifold IsManifold Topology Function
open scoped ContDiff Manifold

noncomputable section
namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

theorem ChartCutoffFamily.boundedAtlas_parentPoint_mem_target
    {G : PreparedCharts M n} {T : ℝ} (Q : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (p : Fin Q.count) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ ((Q.boundedAtlas hT).chart p).target) :
    Q.center p + T⁻¹ • y ∈ (G.chart (Q.parent p)).target :=
  G.buffered _ ((closedBall_subset_closedBall (by linarith [G.radius_pos (Q.parent p)]))
    (ball_subset_closedBall (Q.scaledPoint_in_open_core hT p hy)))

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)

/-- The genuine metric-normalized coefficient equivalence at an actual chart
point. It is built from the actual chart derivative, not supplied independently. -/
def boundedAtlasCoframeEquiv {T : ℝ} (Q : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (p : Fin Q.count) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ ((Q.boundedAtlas hT).chart p).target) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  chartOrthonormalCoframeEquiv g f (G.chart (Q.parent p)) (G.chart_smooth _)
    (Q.center p + T⁻¹ • y) (Q.boundedAtlas_parentPoint_mem_target hT p hy)

@[simp] theorem boundedAtlasCoframeEquiv_coe {T : ℝ} (Q : ChartCutoffFamily G T)
    (hT : 1 ≤ T) (p : Fin Q.count) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ ((Q.boundedAtlas hT).chart p).target) :
    (boundedAtlasCoframeEquiv G g f Q hT p y hy).toContinuousLinearMap =
      actualReferenceCoframe G g f (Q.parent p) (Q.center p) T y := rfl

theorem actualReferenceCoframe_contDiffOn_boundedAtlas {T : ℝ} (Q : ChartCutoffFamily G T)
    (hT : 1 ≤ T) (p : Fin Q.count) :
    ContDiffOn ℝ ∞ (actualReferenceCoframe G g f (Q.parent p) (Q.center p) T)
      ((Q.boundedAtlas hT).chart p).target := by
  have ha : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) ↦ Q.center p + T⁻¹ • z) :=
    contDiff_const.add (contDiff_id.const_smul T⁻¹)
  exact (chartOrthonormalCoframe_contDiffOn g f (G.chart (Q.parent p)) (G.chart_smooth _)).comp
    ha.contDiffOn (fun _ hy ↦ Q.boundedAtlas_parentPoint_mem_target hT p hy)

/-- One positive forward-jet sequence and inverse budget work on all entire
bounded-atlas targets. The coefficient equivalence is the same actual one
defined above. All constants precede every real scale and net choice. -/
theorem exists_boundedAtlas_coframe_geometry :
    ∃ (B : ℕ → ℝ) (L : ℝ), (∀ j, 1 ≤ B j) ∧ 1 ≤ L ∧
      ∀ T : ℝ, ∀ hT : 1 ≤ T, ∀ Q : ChartCutoffFamily G T, ∀ p : Fin Q.count,
        ContDiffOn ℝ ∞ (actualReferenceCoframe G g f (Q.parent p) (Q.center p) T)
          ((Q.boundedAtlas hT).chart p).target ∧
        ∀ y (hy : y ∈ ((Q.boundedAtlas hT).chart p).target),
          ‖(boundedAtlasCoframeEquiv G g f Q hT p y hy).toContinuousLinearMap‖ ≤ B 0 ∧
          ‖(boundedAtlasCoframeEquiv G g f Q hT p y hy).symm.toContinuousLinearMap‖ ≤ L ∧
          (∀ j, ‖iteratedFDeriv ℝ j
              (actualReferenceCoframe G g f (Q.parent p) (Q.center p) T) y‖ ≤ B j * (T⁻¹)^j) ∧
          (∀ j, ‖iteratedFDeriv ℝ j
              (actualReferenceCoframe G g f (Q.parent p) (Q.center p) T) y‖ ≤ B j) ∧
          ‖fderiv ℝ (actualReferenceCoframe G g f (Q.parent p) (Q.center p) T) y‖ ≤ B 1 / T := by
  obtain ⟨B, L, hB, hL, hbound, hinverse⟩ := exists_preparedCoframe_uniform_bounds G g f
  refine ⟨B, L, hB, hL, ?_⟩
  intro T hT Q p
  refine ⟨actualReferenceCoframe_contDiffOn_boundedAtlas G g f Q hT p, ?_⟩
  intro y hy
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hcore : Q.center p + T⁻¹ • y ∈
      closedBall (G.center (Q.parent p)) (4 * G.radius (Q.parent p)) :=
    (closedBall_subset_closedBall (by linarith [G.radius_pos (Q.parent p)]))
      (ball_subset_closedBall (Q.scaledPoint_in_open_core hT p hy))
  have hforward : ‖(boundedAtlasCoframeEquiv G g f Q hT p y hy).toContinuousLinearMap‖ ≤ B 0 := by
    simpa only [boundedAtlasCoframeEquiv_coe, actualReferenceCoframe,
      norm_iteratedFDeriv_zero] using hbound 0 (Q.parent p) _ hcore
  have hinv : ‖(boundedAtlasCoframeEquiv G g f Q hT p y hy).symm.toContinuousLinearMap‖ ≤ L :=
    hinverse (Q.parent p) _ hcore
  have hjets (j : ℕ) : ‖iteratedFDeriv ℝ j
      (actualReferenceCoframe G g f (Q.parent p) (Q.center p) T) y‖ ≤ B j * (T⁻¹)^j := by
    change ‖iteratedFDeriv ℝ j
      (fun z ↦ preparedCoframe G g f (Q.parent p) (Q.center p + T⁻¹ • z)) y‖ ≤ _
    rw [iteratedFDeriv_centered_rescaling _ _ hTpos.ne', norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hTpos.le) _)]
    exact (mul_le_mul_of_nonneg_left (hbound j (Q.parent p) _ hcore) (by positivity)).trans_eq (mul_comm _ _)
  refine ⟨hforward, hinv, hjets, ?_, ?_⟩
  · intro j
    exact (hjets j).trans ((mul_le_mul_of_nonneg_left
      (pow_le_one₀ (inv_nonneg.mpr hTpos.le) (inv_le_one_of_one_le₀ hT))
      (zero_le_one.trans (hB j))).trans_eq (mul_one _))
  · simpa only [norm_iteratedFDeriv_one, pow_one, div_eq_mul_inv] using hjets 1

end GlobalEmbedding.Initialization
