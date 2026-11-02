import Smoothing.ParameterRound2IdentityRawCosts

/-! Finite dependence of the actual identity-chart geometry and mean input
costs. These are equalities of the existing numerical formulas, including the
actual first-frame and true-normal-Hessian transfer. No new estimate or
replacement geometry is supplied. Together with the truncated raw mean cost,
this keeps the validity threshold independent of arbitrary profile tails. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped BigOperators
namespace GlobalEmbedding.Continuation

private theorem transition_prefix_congr (T T' : ℕ → ℝ) (j : ℕ)
    (h : ∀ k, k ≤ j → T k = T' k) :
    bufferedTransitionPrefix T j = bufferedTransitionPrefix T' j := by
  unfold bufferedTransitionPrefix
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact h k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

private theorem fast_cost_prefix_congr (T T' : ℕ → ℝ) (j : ℕ)
    (h : ∀ k, k ≤ j → T k = T' k) :
    actualFastChartTransferCost T j = actualFastChartTransferCost T' j := by
  unfold actualFastChartTransferCost
  rw [transition_prefix_congr T T' j h]

private theorem fast_prefix_congr (T T' : ℕ → ℝ) (j : ℕ)
    (h : ∀ k, k ≤ j → T k = T' k) :
    actualFastChartTransferPrefix T j = actualFastChartTransferPrefix T' j := by
  unfold actualFastChartTransferPrefix
  apply Finset.sum_congr rfl
  intro k hk
  apply fast_cost_prefix_congr
  intro l hl
  exact h l (hl.trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

private theorem first_frame_prefix_congr (T T' : ℕ → ℝ) (j : ℕ)
    (h : ∀ k, k ≤ j+1 → T k = T' k) :
    actualFirstFrameTransferCost T j = actualFirstFrameTransferCost T' j := by
  unfold actualFirstFrameTransferCost
  rw [fast_prefix_congr T T' j (fun k hk => h k (by omega)),
    transition_prefix_congr T T' (j+1) h]

private theorem tensor_cost_prefix_congr (T T' : ℕ → ℝ) (j : ℕ)
    (h : ∀ k, k ≤ j+1 → T k = T' k) :
    actualFastTensorChartTransferCost T j = actualFastTensorChartTransferCost T' j := by
  unfold actualFastTensorChartTransferCost
  rw [fast_prefix_congr T T' j (fun k hk => h k (by omega)),
    transition_prefix_congr T T' (j+1) h]

private theorem normal_transfer_prefix_congr (T T' : ℕ → ℝ) (j : ℕ)
    (h : ∀ k, k ≤ j+1 → T k = T' k) :
    actualNormalChartTransferCost T j = actualNormalChartTransferCost T' j := by
  unfold actualNormalChartTransferCost
  apply Finset.sum_congr rfl
  intro k hk
  apply tensor_cost_prefix_congr
  intro l hl
  exact h l (by have := Finset.mem_range.mp hk; omega)

theorem actualAdaptedUniformGeometryCost_prefix_congr
    (m N j : ℕ) (T T' : ℕ → ℝ) (c cT backBound MA MH : ℝ)
    (h : ∀ k, k ≤ j+2 → T k = T' k) :
    actualAdaptedUniformGeometryCost m N j T c cT backBound MA MH =
      actualAdaptedUniformGeometryCost m N j T' c cT backBound MA MH := by
  have hfirst := first_frame_prefix_congr T T' (j+1) (fun k hk => h k (by omega))
  have hnormal := normal_transfer_prefix_congr T T' j (fun k hk => h k (by omega))
  simp only [actualAdaptedUniformGeometryCost,hfirst,hnormal]

theorem parameterRound2_identityRawMg_prefix_congr
    (m d N n : ℕ) (packet c cT Bnative : ℝ) (T T' : ℕ → ℝ)
    (h : ∀ k, k ≤ n+2 → T k = T' k) :
    parameterRound2_identityRawMg m d N n packet c cT Bnative T =
      parameterRound2_identityRawMg m d N n packet c cT Bnative T' := by
  exact actualAdaptedUniformGeometryCost_prefix_congr m N n T T' c cT Bnative _ _ h

theorem parameterRound2_identityRawDinput_prefix_congr
    (m d n : ℕ) (packet : ℝ) (T T' : ℕ → ℝ)
    (h : ∀ k, k ≤ n → T k = T' k) :
    parameterRound2_identityRawDinput m d n packet T =
      parameterRound2_identityRawDinput m d n packet T' := by
  let a := parameterTensorModelEquiv (m+1) d
  have heq := fast_prefix_congr
    (fun k => ‖a.toContinuousLinearMap‖*T k)
    (fun k => ‖a.toContinuousLinearMap‖*T' k) n (fun k hk => by rw [h k hk])
  dsimp only [parameterRound2_identityRawDinput]
  rw [heq]

theorem parameterRound2_identityRawBnd_prefix_congr
    (m d N n : ℕ) (packet c cT Bnative Meta R : ℝ) (T T' : ℕ → ℝ)
    (h : ∀ k, k ≤ n+2 → T k = T' k) :
    parameterRound2_identityRawBnd m d N n packet c cT Bnative Meta R T =
      parameterRound2_identityRawBnd m d N n packet c cT Bnative Meta R T' := by
  have hfast := fast_prefix_congr T T' n (fun k hk => h k (by omega))
  have hMg := parameterRound2_identityRawMg_prefix_congr m d N n packet c cT Bnative T T' h
  have hD := parameterRound2_identityRawDinput_prefix_congr m d n packet T T'
    (fun k hk => h k (by omega))
  simp only [parameterRound2_identityRawBnd,hfast,hMg,hD]

/-- The real stage geometry/input costs at order n use only inverse-coordinate
orders through n+2. Original packet and meta profiles are read at n itself. -/
theorem parameterRound2_identityRawStageCosts_prefix_congr
    (m d N n : ℕ) (P P' Meta Meta' T T' : ℕ → ℝ) (c cT Bnative R : ℝ)
    (hP : P n = P' n) (hMeta : Meta n = Meta' n)
    (hT : ∀ k, k ≤ n+2 → T k = T' k) :
    parameterRound2_identityRawBnd m d N n (P n) c cT Bnative (Meta n) R T =
      parameterRound2_identityRawBnd m d N n (P' n) c cT Bnative (Meta' n) R T' ∧
    parameterRound2_identityRawMg m d N n (P n) c cT Bnative T =
      parameterRound2_identityRawMg m d N n (P' n) c cT Bnative T' ∧
    parameterRound2_identityRawDinput m d n (P n) T =
      parameterRound2_identityRawDinput m d n (P' n) T' := by
  rw [hP,hMeta]
  exact ⟨parameterRound2_identityRawBnd_prefix_congr m d N n _ c cT Bnative _ R T T' hT,
    parameterRound2_identityRawMg_prefix_congr m d N n _ c cT Bnative T T' hT,
    parameterRound2_identityRawDinput_prefix_congr m d n _ T T' (fun k hk => hT k (by omega))⟩

theorem parameterRound2_identityRawTransition_prefix_congr
    (m d j : ℕ) (P P' Forward Forward' : ℕ → ℝ)
    (hP : ∀ k, k ≤ j → P k = P' k)
    (hF : ∀ k, k ≤ j → Forward k = Forward' k) :
    ∀ k, k ≤ j → parameterRound2_identityRawTransition m d P Forward k =
      parameterRound2_identityRawTransition m d P' Forward' k := by
  intro k hk
  simp only [parameterRound2_identityRawTransition,hP k hk,hF k hk]

#print axioms parameterRound2_identityRawStageCosts_prefix_congr
#print axioms parameterRound2_identityRawTransition_prefix_congr
end GlobalEmbedding.Continuation
