import Smoothing.ParameterRound2UniformMeanFinitePrefix
import Smoothing.ParameterRound2MeanRawGermCostIndex

/-! Exact finite-order dependence of the actual numerical reserve threshold.
Both the target profile and the analytic-cost order may vary. Dependence in the
real size argument is left unrestricted: no false monotonicity is used. The
actual raw mean cost now truncates transitions before Classical.choose, so its
selected value, and not just the existence of a bound, has the stated prefix. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

theorem parameterRound2_uniformMeanProfile_all_prefix_congr
    (B B' : ℕ → ℝ) (C C' : ℕ → ℝ → ℝ) (loss i s : ℕ)
    (hB : ∀ k, k ≤ s+i*loss → B k = B' k)
    (hC : ∀ k, k ≤ s+i*loss → ∀ R, C k R = C' k R) :
    parameterRound2_uniformMeanProfile B C loss i s =
      parameterRound2_uniformMeanProfile B' C' loss i s := by
  induction i generalizing s with
  | zero =>
    exact hB s (by omega)
  | succ i ih =>
    have heq : s+loss+i*loss = s+(i+1)*loss := by
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    have hp := ih (s+loss) (fun k hk => hB k (by omega))
      (fun k hk => hC k (by omega))
    simp only [parameterRound2_uniformMeanProfile,hp]
    rw [hB s (by omega),hC s (by omega)]

theorem parameterRound2_uniformMeanThreshold_all_prefix_congr
    (B B' : ℕ → ℝ) (C C' : ℕ → ℝ → ℝ) (rho : ℝ) (q loss : ℕ)
    (hB : ∀ k, k ≤ q*loss → B k = B' k)
    (hC : ∀ k, k ≤ q*loss → ∀ R, C k R = C' k R) :
    parameterRound2_uniformMeanThreshold B C rho q loss =
      parameterRound2_uniformMeanThreshold B' C' rho q loss := by
  have hsum :
      (∑ i ∈ Finset.range q, max 0 (C 0 (parameterRound2_uniformMeanProfile B C loss i loss))) =
      ∑ i ∈ Finset.range q, max 0 (C' 0 (parameterRound2_uniformMeanProfile B' C' loss i loss)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiq : i+1 ≤ q := by simpa using hi
    have hle : loss+i*loss ≤ q*loss := by
      have hmul := Nat.mul_le_mul_right loss hiq
      simp only [Nat.add_mul,Nat.one_mul] at hmul
      omega
    have hp := parameterRound2_uniformMeanProfile_all_prefix_congr B B' C C' loss i loss
      (fun k hk => hB k (hk.trans hle)) (fun k hk => hC k (hk.trans hle))
    rw [hp,hC 0 (Nat.zero_le _)]
  unfold parameterRound2_uniformMeanThreshold parameterRound2_uniformMeanEntranceCost
  rw [hsum]

universe uM uTr uΛ uΒ
variable {m d N : ℕ} {M : Type uM} {Tr : Type uTr} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]

/-- With scalar raw budgets held fixed, the SAME named reserve threshold uses
B0 through q*(q+4), observer T through q*(q+4)+1, and parameter TP through
q*(q+4). The equality concerns the actual selected raw analytic costs. -/
theorem parameterRound2_rawMeanThreshold_transition_prefix_congr
    (B0 B0' : ℕ → ℝ) (rho : ℝ) (q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s)
    (T TP T' TP' : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k)
    (hT' : ∀ k, 0 ≤ T' k) (hTP' : ∀ k, 0 ≤ TP' k)
    (hB0 : ∀ k, k ≤ q*(q+4) → B0 k = B0' k)
    (hTeq : ∀ k, k ≤ q*(q+4)+1 → T k = T' k)
    (hTPeq : ∀ k, k ≤ q*(q+4) → TP k = TP' k) :
    let C := fun s R => parameterRound2_rawMeanIndexUniformCost.{uM,uTr,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s)
      hc (hBnd s R) (hMg s) T TP hT hTP
    let C' := fun s R => parameterRound2_rawMeanIndexUniformCost.{uM,uTr,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s)
      hc (hBnd s R) (hMg s) T' TP' hT' hTP'
    parameterRound2_uniformMeanThreshold B0 C rho q (q+4) =
      parameterRound2_uniformMeanThreshold B0' C' rho q (q+4) := by
  intro C C'
  apply parameterRound2_uniformMeanThreshold_all_prefix_congr B0 B0' C C' rho q (q+4) hB0
  intro s hs R
  exact parameterRound2_rawMeanIndexUniformCost_prefix_congr
    (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s)
    hc (hBnd s R) (hMg s) T TP T' TP' hT hTP hT' hTP'
    (fun k hk => hTeq k (by omega)) (fun k hk => hTPeq k (hk.trans hs))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.parameterRound2_uniformMeanProfile_all_prefix_congr
#print axioms GlobalEmbedding.Continuation.parameterRound2_uniformMeanThreshold_all_prefix_congr
#print axioms GlobalEmbedding.Continuation.parameterRound2_rawMeanThreshold_transition_prefix_congr
