import OriginalAuxiliary.PreparedParentBounds
import OriginalAuxiliary.NativeChartMargin
import Initialization.Assembly.FullCore

/-!
# Original auxiliary margin for the same canonical scale family

The positive constants are outputs of the fixed initialization data and the
original continuous auxiliary Riemannian norm. They precede both real
frequencies and every chart in the actual T-scale atlas. The same explicit
map `metricInitializationMap` occurs in the chart estimates, intrinsic
margin and every later repair-factory evaluation.

The forward comparison grows as T²; the original intrinsic margin grows
by the same factor. Their quotient is uniformly positive. Requiring the
forward comparison alone to be independent of T would discard this exact
compensation and would impose a false extra geometric requirement.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Initialization GlobalEmbedding.Offline
  Manifold IsManifold Bundle Set Metric
open scoped ContDiff Topology
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace GlobalEmbedding.Continuation.OriginalAuxiliary

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "I" => 𝓘(ℝ, D)

attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
/-- Manufactured scale compensation in the unchanged original auxiliary
norm. No derivative bound, margin comparison, or frequency-dependent
constant is supplied by the caller. -/
theorem InitializationData.exists_original_scale_control
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (m+1)))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
    (data : InitializationData M m) (hm : 1 ≤ m)
    (g : ContMDiffRiemannianMetric I ∞ D (TangentSpace I : M → Type _)) :
    ∃ (B : InitializationReserves) (mu C : ℝ),
      ColoredApproximationCore data.charts g data.frame data.phase.selector B ∧
      0 < mu ∧ 0 < C ∧
      (∀ (T : ℝ) (hT : 1 ≤ T) (i : Fin (initializationAtlas data.charts T hT).count)
        (y : D), y ∈ ((initializationAtlas data.charts T hT).chart i).target →
        ‖mfderiv I I ((initializationAtlas data.charts T hT).chart i)
          (((initializationAtlas data.charts T hT).chart i).symm y)‖^2 ≤ T^2 * C) ∧
      (∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
        B.K₀ ≤ K → B.R₀ * K ≤ T → ∀ x : M,
        T^2 * mu ≤ truePhaseMargin
          (metricInitializationMap data.charts g data.frame data.phase.selector K T hK)
          (data.map_smooth g K T hK) x) := by
  obtain ⟨B, hB⟩ := data.exists_core hm g
  obtain ⟨CF, CI, hCF, hCI, hAux⟩ := prepared_scaled_auxiliary_bounds data.charts
  refine ⟨B, B.margin / CI^2, CF^2, hB,
    div_pos B.margin_pos (sq_pos_of_pos hCI), sq_pos_of_pos hCF, ?_, ?_⟩
  · intro T hT i y hy
    exact (hAux T hT (preparedCutoffsAt data.charts T hT) i y hy).1
  · intro K T hK hKT hK0 hR0 x
    have hT : 1 ≤ T := hK.trans hKT
    have hTp : 0 < T := zero_lt_one.trans_le hT
    let A := initializationAtlas data.charts T hT
    obtain ⟨i, hi⟩ := A.cover x
    have hx : x ∈ (A.chart i).source := A.inner_subset i hi
    have hy : A.chart i x ∈ (A.chart i).target := (A.chart i).map_source hx
    have hInverse := (hAux T hT (preparedCutoffsAt data.charts T hT)
      i (A.chart i x) hy).2
    have hMargin := hB.phase_margin K T hK hKT hK0 hR0 i (A.chart i x) hy
    have hCinv : 0 < (T^2)⁻¹ * CI^2 :=
      mul_pos (inv_pos.mpr (sq_pos_of_pos hTp)) (sq_pos_of_pos hCI)
    have hNative := chart_margin_to_original_native (by simpa using (show 2 ≤ m+1 by omega))
      (metricInitializationMap data.charts g data.frame data.phase.selector K T hK)
      (data.map_smooth g K T hK) (A.chart i) ((hB.atlas_smooth T hT).chart_mem i)
      x hx ((T^2)⁻¹ * CI^2) hCinv hInverse
    have hLower := (div_le_div_of_nonneg_right hMargin hCinv.le).trans hNative
    have hEq : B.margin / ((T^2)⁻¹ * CI^2) = T^2 * (B.margin / CI^2) := by
      field_simp [hTp.ne', hCI.ne']
    exact hEq ▸ hLower

attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
/-- The positive quotient paid to the original phase-to-coordinate bridge
is fixed before the real frequency parameters. -/
theorem compensated_margin_ratio (mu C T : ℝ) (hC : 0 < C) (hT : 0 < T) :
    (T^2 * mu) / (T^2 * C) = mu / C := by
  exact mul_div_mul_left mu C (pow_ne_zero 2 hT.ne')

end GlobalEmbedding.Continuation.OriginalAuxiliary

#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.InitializationData.exists_original_scale_control
#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.compensated_margin_ratio
