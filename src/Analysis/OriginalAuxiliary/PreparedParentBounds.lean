import OriginalAuxiliary.InverseChartBound
import OriginalAuxiliary.RescaledChartDerivative
import Initialization.Geometry.BoundedScaledAtlas

/-!
# One actual auxiliary comparison before all scale refinements

The two constants below are manufactured on the fixed original parent
cores. Their quantifiers precede every real scale and every scale-net
cutoff family. The forward square costs `T^2`; the inverse square gains
`T^(-2)`. The original Riemannian bundle and all chart functions persist.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Initialization Manifold IsManifold
  Set Metric Function Bundle
open scoped ContDiff Topology
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace GlobalEmbedding.Continuation.OriginalAuxiliary

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ, D)

attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
theorem prepared_parent_core_target (G : PreparedCharts M n) (i : Fin G.count) :
    closedBall (G.center i) (2 * G.radius i) ⊆ (G.chart i).target := by
  exact (closedBall_subset_closedBall
    (show 2 * G.radius i ≤ 4 * G.radius i by linarith [G.radius_pos i])).trans (G.buffered i)

attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
/-- Both constants come from the same fixed auxiliary geometry. The finite
sum is over the fixed preparation, never over a receiving scale atlas. -/
theorem prepared_parent_auxiliary_bounds
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)] (G : PreparedCharts M n) :
    ∃ CF CI : ℝ, 0 < CF ∧ 0 < CI ∧
      ∀ i y, y ∈ closedBall (G.center i) (2 * G.radius i) →
        ‖mfderiv I I (G.chart i) ((G.chart i).symm y)‖ ≤ CF ∧
        ‖mfderiv I I (G.chart i).symm y‖ ≤ CI := by
  classical
  have hF (i : Fin G.count) := repair_auxiliary_chart_bound (G.chart i) (G.chart_smooth i)
    (closedBall (G.center i) (2 * G.radius i)) (isCompact_closedBall _ _)
    (prepared_parent_core_target G i)
  have hI (i : Fin G.count) := auxiliary_inverse_chart_bound (G.chart i) (G.chart_smooth i)
    (closedBall (G.center i) (2 * G.radius i)) (isCompact_closedBall _ _)
    (prepared_parent_core_target G i)
  choose CF hCF hFbound using hF
  choose CI hCI hIbound using hI
  refine ⟨1 + ∑ i, CF i, 1 + ∑ i, CI i, ?_, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ ↦ (hCF i).le))
  · exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ ↦ (hCI i).le))
  · intro i y hy
    have hFs : CF i ≤ ∑ j, CF j := Finset.single_le_sum
      (fun j _ ↦ (hCF j).le) (Finset.mem_univ i)
    have hIs : CI i ≤ ∑ j, CI j := Finset.single_le_sum
      (fun j _ ↦ (hCI j).le) (Finset.mem_univ i)
    constructor
    · exact (hFbound i y hy).trans (by linarith)
    · exact (hIbound i y hy).trans (by linarith)


attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
/-- One pair of constants works for every real scale and every actual
scale-net family. Only the explicit, exactly compensated powers of `T`
remain; no maximum over the receiving chart count is taken. -/
theorem prepared_scaled_auxiliary_bounds
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)] (G : PreparedCharts M n) :
    ∃ CF CI : ℝ, 0 < CF ∧ 0 < CI ∧
      ∀ (T : ℝ) (hT : 1 ≤ T) (Q : ChartCutoffFamily G T)
        (i : Fin Q.count) (y : D), y ∈ ((Q.boundedAtlas hT).chart i).target →
        ‖mfderiv I I ((Q.boundedAtlas hT).chart i)
          (((Q.boundedAtlas hT).chart i).symm y)‖^2 ≤ T^2 * CF^2 ∧
        ‖mfderiv I I ((Q.boundedAtlas hT).chart i).symm y‖^2 ≤ (T^2)⁻¹ * CI^2 := by
  obtain ⟨CF, CI, hCF, hCI, hParents⟩ := prepared_parent_auxiliary_bounds G
  refine ⟨CF, CI, hCF, hCI, ?_⟩
  intro T hT Q i y hy
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hyCore : T⁻¹ • y + Q.center i ∈
      closedBall (G.center (Q.parent i)) (2 * G.radius (Q.parent i)) := by
    simpa only [add_comm] using ball_subset_closedBall (Q.scaledPoint_in_open_core hT i hy)
  have hyTarget := prepared_parent_core_target G (Q.parent i) hyCore
  obtain ⟨hForward, hInverse⟩ := hParents (Q.parent i) (T⁻¹ • y + Q.center i) hyCore
  constructor
  · change ‖mfderiv I I (rescaledChart (G.chart (Q.parent i)) (Q.center i) T hTp.ne')
        ((G.chart (Q.parent i)).symm (T⁻¹ • y + Q.center i))‖^2 ≤ _
    rw [rescaledChart_forward_norm_sq _ (G.chart_smooth _) _ _ _ _
      ((G.chart (Q.parent i)).map_target hyTarget)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) hForward 2) (sq_nonneg T)
  · change ‖mfderiv I I
        (rescaledChart (G.chart (Q.parent i)) (Q.center i) T hTp.ne').symm y‖^2 ≤ _
    rw [rescaledChart_inverse_norm_sq _ (G.chart_smooth _) _ _ _ _ hyTarget]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) hInverse 2) (inv_nonneg.mpr (sq_nonneg T))

end GlobalEmbedding.Continuation.OriginalAuxiliary

#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.prepared_parent_auxiliary_bounds

#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.prepared_scaled_auxiliary_bounds
