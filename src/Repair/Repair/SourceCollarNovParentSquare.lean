import Repair.SourceCollarNovParentPrepared

/-! For the actual globally covered auxiliary parent raw family, the local
repaired square normalization is exactly the original square normalization.
This lets either existing smoothing/preparation consumer use the same parent.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

theorem sourceCollarNov_local_normalization_eq_square
    {ι X : Type*} [Fintype ι] (raw : ι → X → ℝ) (hCover : ∀ x, ∃ i, raw i x = 1) :
    tensorLocalNormalizedCutoff raw = squareNormalizedCutoff raw := by
  funext i x
  have hFour := tensorLocalCoverageSum_four_le raw x (hCover x)
  have hTwo : (2 : ℝ) ≤ tensorLocalCoverageSum raw x := by linarith
  have hb : tensorCoverageBump (tensorLocalCoverageSum raw x) = 0 :=
    tensorCoverageBump.zero_of_le_dist (by
      simpa only [tensorCoverageBump,dist_zero_right,Real.norm_eq_abs,
        abs_of_nonneg (tensorLocalCoverageSum_nonneg raw x)] using hTwo)
  have hsum : 0 ≤ squareCutoffSum raw x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hfour : (4 : ℝ)^(-(1/2) : ℝ) = 1/2 := by
    rw [Real.rpow_neg (by norm_num),← Real.sqrt_eq_rpow]
    have hs : Real.sqrt (4 : ℝ) = 2 :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
    rw [hs]
    norm_num
  change (2*raw i x)*reciprocalSquareRoot (squareCutoffSum (tensorLocalAugmentedRaw raw) x) =
    raw i x*reciprocalSquareRoot (squareCutoffSum raw x)
  rw [tensorLocalAugmentedRaw_square_sum,hb,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_add,
    tensorLocalCoverageSum_eq_four_mul]
  unfold reciprocalSquareRoot
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hsum,hfour]
  ring

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {A : BufferedAtlas M E} {B T : ℕ → ℝ} {D : ℕ}

theorem sourceCollarNovParent_original_square_formula (hA : IsSmoothBufferedAtlas A)
    (R : TensorRawCutoffPreparation A B T D) (hB : ∀ j, 0 ≤ B j) :
    sourceCollarNovParent R = squareNormalizedCutoff (sourceCollarNovParentRawPreparation hA R hB).raw :=
  sourceCollarNov_local_normalization_eq_square _ (sourceCollarNovParentRawPreparation hA R hB).plateau_cover

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNovParent_original_square_formula
