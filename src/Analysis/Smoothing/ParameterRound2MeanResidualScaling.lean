import Smoothing.ParameterRound2SymmetricTensorSpace

/-! The actual native finite mean residual passes directly to the fast original
norm and the physical delta-squared scale. No reverse tensor-jet estimate is
needed. Every coefficient remains the original native tensor coefficient. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

 theorem parameterRound2_paperAtlasWeighted_mono_scale
    {a q : ℕ} {ι : Type*} [Fintype ι] (base j : ℕ) (tau ell : ℝ) (hle : tau ≤ ell)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ)) :
    paperAtlasWeighted base j tau f O S ≤ paperAtlasWeighted base j ell f O S := by
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_left (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hle) k) _

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)

theorem parameterRound2_original_mean_residual_fast_scale
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B i).target)
    (E : parameterRound2_originalSymmetricTensorSpace A B) (j : ℕ)
    (tau ell delta R : ℝ) (hle : tau ≤ ell)
    (hR : parameterRound2_originalSymmetricSeminorm A B Omega Q hOmega hQ hOmegaTarget hQTarget ell j E ≤ R) :
    let scaled := fun p x => delta^2 • E.val p x
    paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B scaled)
      (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q univ) ≠ ⊤ ∧
    (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B scaled)
      (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q univ)).toReal ≤ delta^2*R := by
  intro scaled
  let SE : parameterRound2_originalSymmetricTensorSpace A B := delta^2 • E
  let p := parameterRound2_originalSymmetricSeminorm A B Omega Q hOmega hQ hOmegaTarget hQTarget ell j
  have hse : p SE ≤ delta^2*R := by
    change p (delta^2 • E) ≤ _
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg delta)]
    exact mul_le_mul_of_nonneg_left hR (sq_nonneg delta)
  have hfinite := parameterRound2_smoothTensor_weighted_finite A B Omega Q hOmega hQ
    hOmegaTarget hQTarget (parameterRound2_symmetricToSmooth A B SE) j ell
  have hmono := parameterRound2_paperAtlasWeighted_mono_scale 0 j tau ell hle
    (incrementsOriginalTensorCoordinates A B scaled)
    (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q univ)
  refine ⟨ne_top_of_le_ne_top hfinite hmono,?_⟩
  exact (ENNReal.toReal_mono hfinite hmono).trans hse

theorem parameterRound2_mean_q_succ_power_le
    (delta epsilon C : ℝ) (q : ℕ) (he : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (hC : 0 ≤ C) :
    delta^2*(epsilon^(q+1)*C) ≤ delta^2*(epsilon^q*C) := by
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg delta)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one he he1 (by omega)) hC

#print axioms parameterRound2_original_mean_residual_fast_scale
#print axioms parameterRound2_mean_q_succ_power_le
end GlobalEmbedding.Continuation
