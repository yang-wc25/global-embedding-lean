import Smoothing.Round3ParameterMeanLocalEstimates
import Smoothing.ParameterRound2UniformMeanAnalyticPrefix
import Smoothing.ParameterRound2UniformMeanResidualPrefix

/-!
# Finite dependence of the actual general-parameter mean residual

The selected mean norm cost already truncates the observer transition
profile. Here both the raw scalar budgets and the analytic cost profiles
may vary. Equality on an explicit finite prefix implies equality of the
named residual coefficient, including its nested reserve-size arguments.
No monotonicity in the real size argument is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

theorem round4Parameter_uniformMeanResidualCost_all_prefix_congr
    (B B' : ℕ → ℝ) (C C' Cdiff Cdiff' : ℕ → ℝ → ℝ) (loss q j : ℕ)
    (hB : ∀ k, k ≤ j+(q+1)*loss → B k = B' k)
    (hC : ∀ k, k ≤ j+(q+1)*loss → ∀ R, C k R = C' k R)
    (hD : ∀ k, k ≤ j+(q+1)*loss → ∀ R, Cdiff k R = Cdiff' k R) :
    parameterRound2_uniformMeanResidualCost B C Cdiff loss q j =
      parameterRound2_uniformMeanResidualCost B' C' Cdiff' loss q j := by
  induction q generalizing j with
  | zero =>
    have hb := hB (j+loss) (by omega)
    simp only [parameterRound2_uniformMeanResidualCost,parameterRound2_finiteMeanErrorCost,hb]
    rw [hC j (by omega)]
  | succ q ih =>
    have h0 : parameterRound2_uniformMeanProfile B C loss q (j+loss) =
        parameterRound2_uniformMeanProfile B' C' loss q (j+loss) := by
      apply parameterRound2_uniformMeanProfile_all_prefix_congr
      · intro k hk
        apply hB k
        simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at *
        omega
      · intro k hk
        apply hC k
        simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at *
        omega
    have h1 : parameterRound2_uniformMeanProfile B C loss (q+1) (j+loss) =
        parameterRound2_uniformMeanProfile B' C' loss (q+1) (j+loss) := by
      apply parameterRound2_uniformMeanProfile_all_prefix_congr
      · intro k hk
        apply hB k
        simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at *
        omega
      · intro k hk
        apply hC k
        simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at *
        omega
    have hr := ih (j+loss)
      (fun k hk => hB k (by
        simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at *
        omega))
      (fun k hk => hC k (by
        simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at *
        omega))
      (fun k hk => hD k (by
        simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] at *
        omega))
    change max 0 (Cdiff j (max (parameterRound2_uniformMeanProfile B C loss q (j+loss))
        (parameterRound2_uniformMeanProfile B C loss (q+1) (j+loss)))) *
        parameterRound2_uniformMeanResidualCost B C Cdiff loss q (j+loss) = _
    rw [h0,h1,hr,hD j (by omega)]
    rfl

universe uM uTr uP uΛ uΒ
variable {m d N : ℕ} {M : Type uM} {Tr : Type uTr}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]

def round4ParameterMeanResidualCost
    (B0 : ℕ → ℝ) (q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (j : ℕ) : ℝ :=
  let C := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    q Rsub Lprimary hq reserve hc Bnd Mg hBnd hMg T hT
  parameterRound2_uniformMeanResidualCost B0 C (fun s R => C s R*Dinput s) (q+4) q j

theorem round4ParameterMeanSizeCost_prefix_congr
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bnd Bnd' : ℕ → ℝ → ℝ) (Mg Mg' : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s)
    (hBnd' : ∀ s R, 0 ≤ Bnd' s R) (hMg' : ∀ s, 0 ≤ Mg' s)
    (T T' : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hT' : ∀ k, 0 ≤ T' k)
    (s : ℕ) (R : ℝ) (hB : Bnd s R = Bnd' s R) (hM : Mg s = Mg' s)
    (heq : ∀ k, k ≤ s+1 → T k = T' k) :
    round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd Mg hBnd hMg T hT s R =
    round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd' Mg' hBnd' hMg' T' hT' s R := by
  have ht := parameterRound2_numericProfilePrefix_congr (s+1) T T' heq
  unfold round3ParameterMeanSizeCost round3ParameterMeanNormCost
  congr 1
  rw [hB,hM,ht]

/-- The order-j coefficient reads scalar raw profiles through
j+(q+1)*(q+4), and the observer transition profile only one order further. -/
theorem round4ParameterMeanResidualCost_prefix_congr
    (B0 B0' : ℕ → ℝ) (q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bnd Bnd' : ℕ → ℝ → ℝ) (Mg Dinput Mg' Dinput' : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s)
    (hBnd' : ∀ s R, 0 ≤ Bnd' s R) (hMg' : ∀ s, 0 ≤ Mg' s)
    (T T' : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hT' : ∀ k, 0 ≤ T' k)
    (j : ℕ)
    (h0 : ∀ k, k ≤ j+(q+1)*(q+4) → B0 k = B0' k)
    (hB : ∀ k, k ≤ j+(q+1)*(q+4) → ∀ R, Bnd k R = Bnd' k R)
    (hM : ∀ k, k ≤ j+(q+1)*(q+4) → Mg k = Mg' k)
    (hD : ∀ k, k ≤ j+(q+1)*(q+4) → Dinput k = Dinput' k)
    (heq : ∀ k, k ≤ j+(q+1)*(q+4)+1 → T k = T' k) :
    round4ParameterMeanResidualCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      B0 q Rsub Lprimary hq reserve hc Bnd Mg Dinput hBnd hMg T hT j =
    round4ParameterMeanResidualCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      B0' q Rsub Lprimary hq reserve hc Bnd' Mg' Dinput' hBnd' hMg' T' hT' j := by
  let C := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    q Rsub Lprimary hq reserve hc Bnd Mg hBnd hMg T hT
  let C' := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    q Rsub Lprimary hq reserve hc Bnd' Mg' hBnd' hMg' T' hT'
  have hCC (s) (hs : s ≤ j+(q+1)*(q+4)) (R) : C s R = C' s R :=
    round4ParameterMeanSizeCost_prefix_congr q Rsub Lprimary hq reserve hc
      Bnd Bnd' Mg Mg' hBnd hMg hBnd' hMg' T T' hT hT' s R (hB s hs R) (hM s hs)
      (fun k hk => heq k (by omega))
  apply round4Parameter_uniformMeanResidualCost_all_prefix_congr B0 B0' C C'
    (fun s R => C s R*Dinput s) (fun s R => C' s R*Dinput' s) (q+4) q j h0 hCC
  intro s hs R
  rw [hCC s hs R,hD s hs]

theorem round4ParameterMeanThreshold_prefix_congr
    (B0 B0' : ℕ → ℝ) (rho : ℝ) (q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bnd Bnd' : ℕ → ℝ → ℝ) (Mg Mg' : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s)
    (hBnd' : ∀ s R, 0 ≤ Bnd' s R) (hMg' : ∀ s, 0 ≤ Mg' s)
    (T T' : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hT' : ∀ k, 0 ≤ T' k)
    (h0 : ∀ k, k ≤ q*(q+4) → B0 k = B0' k)
    (hB : ∀ k, k ≤ q*(q+4) → ∀ R, Bnd k R = Bnd' k R)
    (hM : ∀ k, k ≤ q*(q+4) → Mg k = Mg' k)
    (heq : ∀ k, k ≤ q*(q+4)+1 → T k = T' k) :
    let C := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd Mg hBnd hMg T hT
    let C' := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd' Mg' hBnd' hMg' T' hT'
    parameterRound2_uniformMeanThreshold B0 C rho q (q+4) =
      parameterRound2_uniformMeanThreshold B0' C' rho q (q+4) := by
  intro C C'
  apply parameterRound2_uniformMeanThreshold_all_prefix_congr B0 B0' C C' rho q (q+4) h0
  intro s hs R
  exact round4ParameterMeanSizeCost_prefix_congr q Rsub Lprimary hq reserve hc
    Bnd Bnd' Mg Mg' hBnd hMg hBnd' hMg' T T' hT hT' s R (hB s hs R) (hM s hs)
    (fun k hk => heq k (by omega))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4Parameter_uniformMeanResidualCost_all_prefix_congr
#print axioms GlobalEmbedding.Continuation.round4ParameterMeanResidualCost_prefix_congr
#print axioms GlobalEmbedding.Continuation.round4ParameterMeanThreshold_prefix_congr
