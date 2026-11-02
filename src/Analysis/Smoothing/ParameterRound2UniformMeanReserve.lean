import Smoothing.ParameterRound2FiniteMeanIteration

/-! A quantitative finite-iteration entrance chosen before H and its seminorms.
Only the supplied numerical bounds B(s) are used in the threshold. No
monotonicity of the analytic costs in their size argument is assumed. -/
noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped BigOperators
namespace GlobalEmbedding.Continuation

def parameterRound2_uniformMeanProfile (B : ℕ → ℝ)
    (C : ℕ → ℝ → ℝ) (loss : ℕ) : ℕ → ℕ → ℝ
  | 0,s => B s
  | i+1,s => B s+max 0 (C s (parameterRound2_uniformMeanProfile B C loss i (s+loss)))

def parameterRound2_uniformMeanEntranceCost (B : ℕ → ℝ)
    (C : ℕ → ℝ → ℝ) (q loss : ℕ) : ℝ :=
  1+∑ i ∈ Finset.range q, max 0 (C 0 (parameterRound2_uniformMeanProfile B C loss i loss))

def parameterRound2_uniformMeanThreshold (B : ℕ → ℝ)
    (C : ℕ → ℝ → ℝ) (rho : ℝ) (q loss : ℕ) : ℝ :=
  min 1 (rho/(2*parameterRound2_uniformMeanEntranceCost B C q loss))

theorem parameterRound2_uniformMeanEntranceCost_pos (B : ℕ → ℝ)
    (C : ℕ → ℝ → ℝ) (q loss : ℕ) :
    0 < parameterRound2_uniformMeanEntranceCost B C q loss := by
  have h : 0 ≤ ∑ i ∈ Finset.range q, max 0 (C 0 (parameterRound2_uniformMeanProfile B C loss i loss)) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  dsimp only [parameterRound2_uniformMeanEntranceCost]
  linarith

theorem parameterRound2_uniformMeanThreshold_pos (B : ℕ → ℝ)
    (C : ℕ → ℝ → ℝ) (rho : ℝ) (hrho : 0 < rho) (q loss : ℕ) :
    0 < parameterRound2_uniformMeanThreshold B C rho q loss ∧
      parameterRound2_uniformMeanThreshold B C rho q loss ≤ 1 := by
  exact ⟨lt_min (by norm_num) (div_pos hrho
    (mul_pos (by norm_num) (parameterRound2_uniformMeanEntranceCost_pos B C q loss))),min_le_left _ _⟩

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem parameterRound2_uniform_mean_reserve_profile
    (B : ℕ → ℝ) (Csize : ℕ → ℝ → ℝ) (rho : ℝ) (hrho : 0 < rho) (q loss : ℕ)
    (p : ℕ → Seminorm ℝ V) (H : V) (hH : ∀ s, p s H ≤ B s)
    (T : ℝ → {A : V // p 0 (A-H) < rho} → V)
    (hsize : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (A : {A : V // p 0 (A-H) < rho}),
      p (s+loss) A.val ≤ R → p s (T epsilon A) ≤ epsilon*Csize s R)
    (epsilon : ℝ) (he : 0 < epsilon)
    (he0 : epsilon < parameterRound2_uniformMeanThreshold B Csize rho q loss) :
    let A := fun i : ℕ => (meanReserveStep (p 0) H rho (T epsilon))^[i] H
    let R := parameterRound2_uniformMeanProfile B Csize loss
    (∀ i ≤ q, p 0 (A i-H) ≤ rho/2) ∧
      (∀ i ≤ q, ∀ s, p s (A i) ≤ R i s) := by
  intro A R
  let M := parameterRound2_uniformMeanEntranceCost B Csize q loss
  have hM : 0 < M := parameterRound2_uniformMeanEntranceCost_pos B Csize q loss
  have he1 : epsilon ≤ 1 := he0.le.trans (min_le_left _ _)
  have heM : epsilon*M ≤ rho/2 := by
    have hh := (lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hM)).mp
      (he0.trans_le (min_le_right _ _))
    nlinarith
  have hMi (i : ℕ) (hi : i < q) : max 0 (Csize 0 (R i loss)) ≤ M := by
    have hh : max 0 (Csize 0 (R i loss)) ≤
        ∑ k ∈ Finset.range q, max 0 (Csize 0 (R k loss)) :=
      Finset.single_le_sum (f := fun k => max 0 (Csize 0 (R k loss)))
        (fun k hk => le_max_left _ _) (Finset.mem_range.mpr hi)
    dsimp only [M,parameterRound2_uniformMeanEntranceCost]
    linarith
  have hboth : ∀ i ≤ q, p 0 (A i-H) ≤ rho/2 ∧ ∀ s, p s (A i) ≤ R i s := by
    intro i
    induction i with
    | zero =>
      intro hi
      refine ⟨?_,fun s => hH s⟩
      change p 0 (H-H) ≤ rho/2
      simpa only [sub_self,map_zero] using (div_nonneg hrho.le (by norm_num : (0:ℝ)≤2))
    | succ i ih =>
      intro hi
      have hiq : i ≤ q := by omega
      have hiq' : i < q := by omega
      have hh := ih hiq
      have hdom : p 0 (A i-H) < rho := hh.1.trans_lt (by linarith)
      have hstep : A (i+1) = H-T epsilon ⟨A i,hdom⟩ := by
        change (meanReserveStep (p 0) H rho (T epsilon))^[i+1] H = _
        rw [Function.iterate_succ_apply']
        change meanReserveStep (p 0) H rho (T epsilon) (A i) = _
        simp only [meanReserveStep,dite_eq_left hdom]
      have ht (s : ℕ) := hsize epsilon he he1 s (R i (s+loss)) ⟨A i,hdom⟩ (hh.2 (s+loss))
      constructor
      · have heq : A (i+1)-H = -(T epsilon ⟨A i,hdom⟩) := by rw [hstep]; abel
        change p 0 (A (i+1)-H) ≤ _
        rw [heq,map_neg_eq_map]
        calc
          _ ≤ epsilon*Csize 0 (R i loss) := by simpa only [zero_add] using ht 0
          _ ≤ epsilon*max 0 (Csize 0 (R i loss)) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) he.le
          _ ≤ epsilon*M := mul_le_mul_of_nonneg_left (hMi i hiq') he.le
          _ ≤ rho/2 := heM
      · intro s
        change p s (A (i+1)) ≤ _
        rw [hstep]
        calc
          _ ≤ p s H+p s (T epsilon ⟨A i,hdom⟩) := map_sub_le_add _ _ _
          _ ≤ B s+epsilon*Csize s (R i (s+loss)) := add_le_add (hH s) (ht s)
          _ ≤ B s+epsilon*max 0 (Csize s (R i (s+loss))) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_max_right _ _) he.le)
          _ ≤ B s+max 0 (Csize s (R i (s+loss))) :=
            add_le_add le_rfl (by simpa only [one_mul] using
              mul_le_mul_of_nonneg_right he1 (le_max_left 0 _))
          _ = R (i+1) s := rfl
  exact ⟨fun i hi => (hboth i hi).1,fun i hi => (hboth i hi).2⟩

#print axioms parameterRound2_uniformMeanThreshold_pos
#print axioms parameterRound2_uniform_mean_reserve_profile
end GlobalEmbedding.Continuation
