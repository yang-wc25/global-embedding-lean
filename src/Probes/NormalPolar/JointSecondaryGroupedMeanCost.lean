import NormalPolar.JointSecondaryGroupedMean
import Smoothing.ParameterRound2TensorSeminorm

/-! Explicit original-label grouped mean costs. The subordinate counts occur
inside each amplitude coefficient before squaring. The exact amplitude-square
factor allows the initial global parameter cutoff to be chosen from primitive
source budgets before any oscillation scale, with no forcing output premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped BigOperators Classical
namespace GlobalEmbedding.Continuation

def jointGroupedPrescribedMeanUniformCost {r : ℕ}
    (Sub : Fin r → Type*) [∀ l, Fintype (Sub l)]
    (m N p n length j : ℕ) (T : ℕ → ℝ) (weight : Fin r → ℝ)
    (Mg Bchi Bnu Mphase Ku : ℝ) : ℝ :=
  ∑ co : Fin (m+1) × Fin (m+1),
    2^j*‖incrementsMeanBilinear (Λ := Fin r) (N := N) co.1 co.2‖*
      (∑ l, (Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost
        m N p n length j T (weight l) Mg Bchi Bnu Mphase Ku)^2

theorem jointGroupedPrescribedMeanUniformCost_nonneg {r : ℕ}
    (Sub : Fin r → Type*) [∀ l, Fintype (Sub l)]
    (m N p n length j : ℕ) (T : ℕ → ℝ) (weight : Fin r → ℝ)
    (Mg Bchi Bnu Mphase Ku : ℝ) :
    0 ≤ jointGroupedPrescribedMeanUniformCost Sub m N p n length j T weight Mg Bchi Bnu Mphase Ku := by
  apply Finset.sum_nonneg
  intro co _
  exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) j)
    (ContinuousLinearMap.opNorm_nonneg _)) (sq_nonneg _)

theorem jointGroupedPrescribedMeanUniformCost_component {r : ℕ}
    (Sub : Fin r → Type*) [∀ l, Fintype (Sub l)]
    (m N p n length j : ℕ) (T : ℕ → ℝ) (weight : Fin r → ℝ)
    (Mg Bchi Bnu Mphase Ku : ℝ) (i q : Fin (m+1)) :
    2^j*‖incrementsMeanBilinear (Λ := Fin r) (N := N) i q‖*
      (∑ l, (Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost
        m N p n length j T (weight l) Mg Bchi Bnu Mphase Ku)^2 ≤
      jointGroupedPrescribedMeanUniformCost Sub m N p n length j T weight Mg Bchi Bnu Mphase Ku := by
  unfold jointGroupedPrescribedMeanUniformCost
  apply Finset.single_le_sum (f := fun co : Fin (m+1) × Fin (m+1) =>
    2^j*‖incrementsMeanBilinear (Λ := Fin r) (N := N) co.1 co.2‖*
      (∑ l, (Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost
        m N p n length j T (weight l) Mg Bchi Bnu Mphase Ku)^2)
    (fun co _ => ?_) (Finset.mem_univ (i,q))
  exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) j)
    (ContinuousLinearMap.opNorm_nonneg _)) (sq_nonneg _)

theorem jointGroupedPrescribedMeanUniformCost_amplitude_sq {r : ℕ}
    (Sub : Fin r → Type*) [∀ l, Fintype (Sub l)]
    (m N p n length j : ℕ) (T : ℕ → ℝ) (weight : Fin r → ℝ)
    (Mg Bchi Bnu Mphase amplitude : ℝ) :
    jointGroupedPrescribedMeanUniformCost Sub m N p n length j T weight Mg Bchi Bnu Mphase amplitude =
      jointGroupedPrescribedMeanUniformCost Sub m N p n length j T weight Mg Bchi Bnu Mphase 1 * amplitude^2 := by
  have hs : (∑ l, (Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost
      m N p n length j T (weight l) Mg Bchi Bnu Mphase amplitude) =
      (∑ l, (Fintype.card (Sub l) : ℝ)*actualVariablePrescribedCoefficientCost
        m N p n length j T (weight l) Mg Bchi Bnu Mphase 1)*amplitude := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    unfold actualVariablePrescribedCoefficientCost
    ring
  unfold jointGroupedPrescribedMeanUniformCost
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro co _
  rw [hs]
  ring

def jointGroupedPrescribedZeroSourceCost {r : ℕ}
    (Sub : Fin r → Type*) [∀ l, Fintype (Sub l)]
    (m N d p n length : ℕ) (T : ℕ → ℝ) (weight : Fin r → ℝ)
    (Mg Bchi Bnu Mphase : ℝ) : ℝ :=
  linearModelFactor (parameterTensorModelEquiv (m+1) d).symm 0 *
    jointGroupedPrescribedMeanUniformCost Sub m N p n length 0 T weight Mg Bchi Bnu Mphase 1

theorem jointGroupedPrescribedZeroSourceCost_nonneg {r : ℕ}
    (Sub : Fin r → Type*) [∀ l, Fintype (Sub l)]
    (m N d p n length : ℕ) (T : ℕ → ℝ) (weight : Fin r → ℝ)
    (Mg Bchi Bnu Mphase : ℝ) :
    0 ≤ jointGroupedPrescribedZeroSourceCost Sub m N d p n length T weight Mg Bchi Bnu Mphase :=
  mul_nonneg (linearModelFactor_nonneg _ 0)
    (jointGroupedPrescribedMeanUniformCost_nonneg Sub m N p n length 0 T weight Mg Bchi Bnu Mphase 1)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointGroupedPrescribedMeanUniformCost_amplitude_sq
#print axioms GlobalEmbedding.Continuation.jointGroupedPrescribedZeroSourceCost_nonneg
