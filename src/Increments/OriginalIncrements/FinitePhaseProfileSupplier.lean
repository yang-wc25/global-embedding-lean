import OriginalIncrements.PositiveBudgetMonotonicity

/-!
# Actual adapted charts manufacture finite-prefix positive jet profiles

The chosen chart depends only on the original phase, low-order geometric
reserve, and ball. It is fixed before every higher derivative order, sample
set, weight, or higher phase-jet budget. Both native profiles below are
explicit numerical expressions in the original phase prefix. No chart-value
bound or inverse-jet estimate is assumed. This is the local phase-chart
producer in the proof of `lem:increments`, not a complete global increment.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation.OriginalIncrements

def phaseForwardBudget (M : ℝ) (Phase : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else if j = 1 then 2*(1+2*M) else 2^(j+1)*Phase j

def phaseInverseBudget (mu M : ℝ) (Phase : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else actualEuclideanPhaseSampleInverseJetCost mu M
    (bufferedTransitionPrefix (incrementsCompletionPositiveSlots Phase) j) (j-1)

theorem phaseForwardBudget_nonneg (M : ℝ) (hM : 0 ≤ M) (Phase : ℕ → ℝ)
    (hPhase : ∀ k, 1 ≤ k → 0 ≤ Phase k) (j : ℕ) :
    0 ≤ phaseForwardBudget M Phase j := by
  unfold phaseForwardBudget
  split_ifs with h0 h1
  · exact le_rfl
  · positivity
  · exact mul_nonneg (by positivity) (hPhase j (by omega))

theorem phaseInverseBudget_nonneg (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (Phase : ℕ → ℝ) (hPhase : ∀ k, 1 ≤ k → 0 ≤ Phase k) (j : ℕ) :
    0 ≤ phaseInverseBudget mu M Phase j := by
  unfold phaseInverseBudget
  split_ifs
  · exact le_rfl
  · exact actualEuclideanPhaseSampleInverseJetCost_nonneg hmu hM
      (zero_le_one.trans (one_le_bufferedTransitionPrefix
        (incrementsCompletionPositiveSlots_nonneg Phase hPhase) j)) (j-1)

theorem phase_positive_prefix_bound (Phase : ℕ → ℝ)
    (hPhase : ∀ k, 1 ≤ k → 0 ≤ Phase k) {k j : ℕ} (hk : 1 ≤ k) (hkj : k ≤ j) :
    Phase k ≤ bufferedTransitionPrefix (incrementsCompletionPositiveSlots Phase) j := by
  have h := Finset.single_le_sum
    (fun l (_ : l ∈ Finset.range (j+1)) => incrementsCompletionPositiveSlots_nonneg Phase hPhase l)
    (show k ∈ Finset.range (j+1) by simpa using hkj)
  rw [incrementsCompletionPositiveSlots_of_pos Phase k hk] at h
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

theorem phase_profiles_prefix_congr
    (mu M : ℝ) (Phase Phase' : ℕ → ℝ) (j : ℕ)
    (hP : ∀ k, 1 ≤ k → k ≤ j → Phase k = Phase' k) :
    phaseForwardBudget M Phase j = phaseForwardBudget M Phase' j ∧
    phaseInverseBudget mu M Phase j = phaseInverseBudget mu M Phase' j := by
  constructor
  · unfold phaseForwardBudget
    split_ifs with h0 h1
    · rfl
    · rfl
    · rw [hP j (by omega) le_rfl]
  · unfold phaseInverseBudget
    split_ifs
    · rfl
    · rw [incrementsCompletionPositiveSlots_prefix_congr Phase Phase' j hP]

theorem phase_profiles_mono_prefix
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (Phase Phase' : ℕ → ℝ) (hPhase : ∀ k, 1 ≤ k → 0 ≤ Phase k) (j : ℕ)
    (hP : ∀ k, 1 ≤ k → k ≤ j → Phase k ≤ Phase' k) :
    phaseForwardBudget M Phase j ≤ phaseForwardBudget M Phase' j ∧
    phaseInverseBudget mu M Phase j ≤ phaseInverseBudget mu M Phase' j := by
  constructor
  · unfold phaseForwardBudget
    split_ifs with h0 h1
    · exact le_rfl
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_left (hP j (by omega) le_rfl) (by positivity)
  · unfold phaseInverseBudget
    split_ifs
    · exact le_rfl
    · exact phase_sample_inverse_cost_mono hmu hM
        (zero_le_one.trans (one_le_bufferedTransitionPrefix
          (incrementsCompletionPositiveSlots_nonneg Phase hPhase) j))
        (positive_prefix_mono Phase Phase' j hP) (j-1)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep]
  {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

/-- One actual chart is produced before all observing orders and sample
sets. Each positive native jet estimate reads only original phase jets
through its own order at the actual inverse sample points. -/
theorem exists_actual_chart_with_finite_phase_budgets
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (psi : X → ℝ) (z0 : X) (rho : ℝ) (hrho : 0 < rho)
    (hpsi : ContDiffOn ℝ ∞ psi (ball z0 rho))
    (hspatial : mu ≤ ‖(fderiv ℝ psi z0).comp (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hfirst : ∀ z ∈ ball z0 rho, ‖fderiv ℝ psi z‖ ≤ M)
    (hsecond : ∀ z ∈ ball z0 rho, rho*‖iteratedFDeriv ℝ 2 psi z‖ ≤ M) :
    ∃ a : OpenPartialHomeomorph X X,
      ball z0 (actualEuclideanPhaseRadius mu M rho) ⊆ a.source ∧
      a.source ⊆ ball z0 rho ∧
      ContDiffOn ℝ ∞ a a.source ∧ ContDiffOn ℝ ∞ a.symm a.target ∧
      (∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = psi z) ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧ psi (a.symm z) = z.2 0) ∧
      closedBall (a z0) ((actualEuclideanPhaseRadius mu M rho)/
        (4*actualPhaseInverseConstant mu (2*M))) ⊆ a.target ∧
      ∀ (S : Set X), S ⊆ a.target → ∀ (ell : ℝ) (Phase : ℕ → ℝ),
        0 < ell → (∀ k, 1 ≤ k → 0 ≤ Phase k) →
        ∀ j, 1 ≤ j →
          (∀ k, 2 ≤ k → k ≤ j → ∀ x ∈ a.symm '' S,
            ell^(k-1)*‖iteratedFDeriv ℝ k psi x‖ ≤ Phase k) →
          (∀ x ∈ a.symm '' S,
            ell^(j-1)*‖iteratedFDeriv ℝ j a x‖ ≤ phaseForwardBudget M Phase j) ∧
          (∀ y ∈ S,
            ell^(j-1)*‖iteratedFDeriv ℝ j a.symm y‖ ≤ phaseInverseBudget mu M Phase j) := by
  obtain ⟨a,hi,ho,ha,hai,hp,hpi,ht,hfirstA,hpoint,hInverse⟩ :=
    actual_exists_native_euclidean_quantitative_phase_chart_sample_jets
      mu M hmu hM psi z0 rho hrho hpsi hspatial hfirst hsecond
  refine ⟨a,hi,ho,ha,hai,hp,hpi,ht,?_⟩
  intro S hS ell Phase hell hPhase j hj hPhaseJets
  have hxSource (x : X) (hx : x ∈ a.symm '' S) : x ∈ a.source := by
    obtain ⟨y,hy,rfl⟩ := hx
    exact a.map_target (hS hy)
  constructor
  · intro x hx
    by_cases hj1 : j = 1
    · subst j
      simpa [phaseForwardBudget,norm_iteratedFDeriv_one] using hfirstA x (hxSource x hx)
    · have hj2 : 2 ≤ j := by omega
      have hjSucc : j-1+1 = j := by omega
      have hpow : j-1+2 = j+1 := by omega
      have hpj := hpoint (j-1) (by omega) x (hxSource x hx)
      rw [hjSucc,hpow] at hpj
      calc
        ell^(j-1)*‖iteratedFDeriv ℝ j a x‖ ≤
            ell^(j-1)*(2^(j+1)*‖iteratedFDeriv ℝ j psi x‖) :=
          mul_le_mul_of_nonneg_left hpj (pow_nonneg hell.le _)
        _ = 2^(j+1)*(ell^(j-1)*‖iteratedFDeriv ℝ j psi x‖) := by ring
        _ ≤ 2^(j+1)*Phase j := mul_le_mul_of_nonneg_left
          (hPhaseJets j hj2 le_rfl x hx) (by positivity)
        _ = phaseForwardBudget M Phase j := by
          simp only [phaseForwardBudget,ite_eq_right (show j ≠ 0 by omega),ite_eq_right hj1]
  · have hPrefix0 : 0 ≤ bufferedTransitionPrefix (incrementsCompletionPositiveSlots Phase) j :=
      zero_le_one.trans (one_le_bufferedTransitionPrefix
        (incrementsCompletionPositiveSlots_nonneg Phase hPhase) j)
    have hInv := hInverse S hS (j-1) ell
      (bufferedTransitionPrefix (incrementsCompletionPositiveSlots Phase) j) hell hPrefix0
      (by
        intro k hk hkj x hx
        have horder : k+1 ≤ j := by omega
        have hh := hPhaseJets (k+1) (by omega) horder x hx
        simp only [Nat.add_sub_cancel] at hh
        exact hh.trans (phase_positive_prefix_bound Phase hPhase (by omega) horder))
      j hj (by omega)
    intro y hy
    simpa only [phaseInverseBudget,ite_eq_right (show j ≠ 0 by omega)] using hInv y hy

end GlobalEmbedding.Continuation.OriginalIncrements

#print axioms GlobalEmbedding.Continuation.OriginalIncrements.phase_profiles_mono_prefix
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.exists_actual_chart_with_finite_phase_budgets
