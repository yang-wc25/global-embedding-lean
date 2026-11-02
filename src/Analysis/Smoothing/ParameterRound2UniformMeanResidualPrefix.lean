import Smoothing.ParameterRound2UniformMeanFinitePrefix
import Smoothing.ParameterRound2UniformMeanIteration

/-! Exact finite dependence on the reference profile. The entrance threshold
uses q*loss; the order-j final residual coefficient uses only
j+(q+1)*loss. These are derivatives of the numerical profile of the same
smoothed target and fixed reference, not additional raw tensor assumptions. -/
noncomputable section
open GlobalEmbedding.Paper Set Function
namespace GlobalEmbedding.Continuation

def parameterRound2_uniformMeanResidualCost (B : ℕ → ℝ)
    (C Cdiff : ℕ → ℝ → ℝ) (loss q j : ℕ) : ℝ :=
  let R := parameterRound2_uniformMeanProfile B C loss
  let C0 := fun s => max 0 (C s (B (s+loss)))
  let Cd := fun i s => max 0 (Cdiff s (max (R i (s+loss)) (R (i+1) (s+loss))))
  parameterRound2_finiteMeanErrorCost C0 Cd loss q j

theorem parameterRound2_uniformMeanResidualCost_prefix_congr
    (B B' : ℕ → ℝ) (C Cdiff : ℕ → ℝ → ℝ) (loss q j : ℕ)
    (hB : ∀ k, k ≤ j+(q+1)*loss → B k = B' k) :
    parameterRound2_uniformMeanResidualCost B C Cdiff loss q j =
      parameterRound2_uniformMeanResidualCost B' C Cdiff loss q j := by
  induction q generalizing j with
  | zero =>
    have hb := hB (j+loss) (by omega)
    simp only [parameterRound2_uniformMeanResidualCost,parameterRound2_finiteMeanErrorCost,hb]
  | succ q ih =>
    have h0 : parameterRound2_uniformMeanProfile B C loss q (j+loss) =
        parameterRound2_uniformMeanProfile B' C loss q (j+loss) := by
      apply parameterRound2_uniformMeanProfile_prefix_congr
      intro k hk
      apply hB k
      simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at *
      omega
    have h1 : parameterRound2_uniformMeanProfile B C loss (q+1) (j+loss) =
        parameterRound2_uniformMeanProfile B' C loss (q+1) (j+loss) := by
      apply parameterRound2_uniformMeanProfile_prefix_congr
      intro k hk
      apply hB k
      simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at *
      omega
    have hr := ih (j+loss) (by
      intro k hk
      apply hB k
      simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at *
      omega)
    change max 0 (Cdiff j (max (parameterRound2_uniformMeanProfile B C loss q (j+loss))
        (parameterRound2_uniformMeanProfile B C loss (q+1) (j+loss)))) *
        parameterRound2_uniformMeanResidualCost B C Cdiff loss q (j+loss) = _
    rw [h0,h1,hr]
    rfl

theorem parameterRound2_uniformMeanResidualCost_finite_prefix
    (B : ℕ → ℝ) (C Cdiff : ℕ → ℝ → ℝ) (loss q j : ℕ) :
    parameterRound2_uniformMeanResidualCost B C Cdiff loss q j =
      parameterRound2_uniformMeanResidualCost
        (fun s => if s ≤ j+(q+1)*loss then B s else 0) C Cdiff loss q j := by
  exact parameterRound2_uniformMeanResidualCost_prefix_congr B _ C Cdiff loss q j
    (fun k hk => by simp only [ite_eq_left hk])

#print axioms parameterRound2_uniformMeanResidualCost_prefix_congr
#print axioms parameterRound2_uniformMeanResidualCost_finite_prefix
end GlobalEmbedding.Continuation
