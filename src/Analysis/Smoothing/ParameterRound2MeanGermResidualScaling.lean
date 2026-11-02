import Smoothing.ParameterRound2TensorGermSpace
import Smoothing.ParameterRound2MeanResidualScaling

/-! The actual native finite mean residual passes directly to the fast original
norm and the physical delta-squared scale. No reverse tensor-jet estimate is
needed. Every coefficient remains the original native tensor coefficient. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)

theorem parameterRound2_original_germ_mean_residual_fast_scale
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (E : parameterRound2_originalTensorGermSpace A B S W) (j : ℕ)
    (tau ell delta R : ℝ) (hle : tau ≤ ell)
    (hR : parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell j E ≤ R) :
    let scaled := fun p x => delta^2 • E.val p x
    paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B scaled)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B scaled)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ delta^2*R := by
  intro scaled
  let SE : parameterRound2_originalTensorGermSpace A B S W := delta^2 • E
  let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell j
  have hse : p SE ≤ delta^2*R := by
    change p (delta^2 • E) ≤ _
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg delta)]
    exact mul_le_mul_of_nonneg_left hR (sq_nonneg delta)
  have hfinite := parameterRound2_tensorGerm_weighted_finite A B S W hS hSO SE 0 j ell
  have hmono := parameterRound2_paperAtlasWeighted_mono_scale 0 j tau ell hle
    (incrementsOriginalTensorCoordinates A B scaled)
    (incrementsOriginalDifferentiation A B) S
  refine ⟨ne_top_of_le_ne_top hfinite hmono,?_⟩
  exact (ENNReal.toReal_mono hfinite hmono).trans hse

#print axioms parameterRound2_original_germ_mean_residual_fast_scale
end GlobalEmbedding.Continuation
