import Probes.Round3RepairClosedStateUpdate

/-! A genuine next state from the literal same SF, SH and global U.
Both stay and advance are covered.  The old and new states use exactly one
fixed Ω/Q domain; all higher-order recurrences survive in the result. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round3RepairEntryChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairEntryIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)



/-- A positive finite numerical entrance, evaluated solely from fixed
reference norms and the selected all-order costs at finitely many orders. -/
def round3RepairClosedNumericalThreshold (Cmap Cpair Cd : ℕ → ℝ)
    (budget epsilon eta : ℝ) (k : ℕ) : ℝ :=
  min ((1/2 : ℝ)^5) (min (epsilon/(8*(Cmap (k/2)+1)))
    (min ((budget/(4*(max (round3RepairClosedStateRate packet Cpair budget (40*(k+1)))
      (round3RepairClosedStateRate packet Cpair budget (40*(k+2)))*(1+budget)+1)))^5)
      ((eta/(2*Cd 0*(1+budget)^2+1))^5)))

private theorem round3_repair_fifth_root_bound {t a : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hle : t ≤ a^5) : t^(1/5 : ℝ) ≤ a := by
  have h := Real.rpow_le_rpow ht hle (by norm_num : (0:ℝ) ≤ 1/5)
  have heq : (a^5)^(1/5 : ℝ) = a := by
    rw [← Real.rpow_natCast_mul ha]
    norm_num
  exact h.trans_eq heq

theorem round3_repair_closed_numerical_threshold
    (Cmap Cpair Cd : ℕ → ℝ) (hCmap : ∀ j, 0 ≤ Cmap j)
    (hCpair : ∀ j, 0 ≤ Cpair j) (hCd : ∀ j, 0 ≤ Cd j)
    (budget epsilon eta : ℝ) (hbudget : 0 < budget) (heps : 0 < epsilon) (heta : 0 < eta)
    (k : ℕ) :
    0 < round3RepairClosedNumericalThreshold packet Cmap Cpair Cd budget epsilon eta k ∧
    ∀ (t : ℝ), 0 < t → t ≤ round3RepairClosedNumericalThreshold packet Cmap Cpair Cd budget epsilon eta k →
      t ≤ (1/2 : ℝ)^5 ∧ t ≤ epsilon/(8*(Cmap (k/2)+1)) ∧
      (∀ (s : ℕ), k ≤ s → s ≤ k+1 →
        round3RepairClosedStateRate packet Cpair budget (40*(s+1))*t^(1/5 : ℝ)*(1+budget) ≤ 3*budget/4) ∧
      (2*Cd 0*(1+budget))*t^(1/5 : ℝ)*(1+budget) ≤ eta := by
  let R0 := round3RepairClosedStateRate packet Cpair budget (40*(k+1))
  let R1 := round3RepairClosedStateRate packet Cpair budget (40*(k+2))
  have hRate (j : ℕ) : 0 ≤ round3RepairClosedStateRate packet Cpair budget j := by
    dsimp only [round3RepairClosedStateRate]
    exact add_nonneg (by positivity) (mul_nonneg (mul_nonneg (by norm_num) (hCpair j)) (by linarith))
  have hmax : 0 ≤ max R0 R1 := (hRate _).trans (le_max_left _ _)
  let Cp := max R0 R1*(1+budget)+1
  let Ct := 2*Cd 0*(1+budget)^2+1
  have hCp : 0 < Cp := by dsimp only [Cp]; positivity
  have hCt : 0 < Ct := by dsimp only [Ct]; nlinarith [mul_nonneg (hCd 0) (sq_nonneg (1+budget))]
  have ha : 0 < budget/(4*Cp) := div_pos hbudget (mul_pos (by norm_num) hCp)
  have hb : 0 < eta/Ct := div_pos heta hCt
  have hc : 0 < epsilon/(8*(Cmap (k/2)+1)) := div_pos heps (by have := hCmap (k/2); positivity)
  refine ⟨by
    change 0 < min ((1/2 : ℝ)^5) (min (epsilon/(8*(Cmap (k/2)+1))) (min ((budget/(4*Cp))^5) ((eta/Ct)^5)))
    exact lt_min (by norm_num) (lt_min hc (lt_min (pow_pos ha _) (pow_pos hb _))),?_⟩
  intro t ht htEntry
  change t ≤ min ((1/2 : ℝ)^5) (min (epsilon/(8*(Cmap (k/2)+1)))
    (min ((budget/(4*Cp))^5) ((eta/Ct)^5))) at htEntry
  have htHalf := htEntry.trans (min_le_left _ _)
  have htRest := htEntry.trans (min_le_right _ _)
  have htDisp := htRest.trans (min_le_left _ _)
  have htCosts := htRest.trans (min_le_right _ _)
  have hRootP := round3_repair_fifth_root_bound ht.le ha.le (htCosts.trans (min_le_left _ _))
  have hRootT := round3_repair_fifth_root_bound ht.le hb.le (htCosts.trans (min_le_right _ _))
  have hRoot0 : 0 ≤ t^(1/5 : ℝ) := Real.rpow_nonneg ht.le _
  have hPayP := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 4) hCp)).mp hRootP
  have hPayT := (le_div_iff₀ hCt).mp hRootT
  refine ⟨htHalf,htDisp,?_,?_⟩
  · intro s hks hs
    have hcase : s=k ∨ s=k+1 := by omega
    have hR : round3RepairClosedStateRate packet Cpair budget (40*(s+1)) ≤ max R0 R1 := by
      rcases hcase with rfl | rfl
      · exact le_max_left _ _
      · simpa only [Nat.add_assoc] using (le_max_right R0 R1)
    have hRp := mul_le_mul_of_nonneg_right hR (show 0 ≤ 1+budget by linarith)
    have hCpLe : round3RepairClosedStateRate packet Cpair budget (40*(s+1))*(1+budget) ≤ Cp := by
      dsimp only [Cp]
      linarith
    have hSmall := mul_le_mul_of_nonneg_right hCpLe hRoot0
    nlinarith only [hSmall,hPayP,hbudget]
  · have hSmall : 2*Cd 0*(1+budget)^2*t^(1/5 : ℝ) ≤ Ct*t^(1/5 : ℝ) := by
      exact mul_le_mul_of_nonneg_right (by dsimp only [Ct]; linarith) hRoot0
    nlinarith only [hSmall,hPayT]

/-- Named finite entrance applied immediately to the actual same-U update. -/
theorem round3_repair_named_closed_state_update [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ) (k : ℕ) (hk : 10 ≤ k) :
    ∃ Cs : ℕ → ℝ, (∀ j, 0 ≤ Cs j) ∧ ∀ (Cmap Cmetric : ℕ → ℝ),
    (∀ j, 0 ≤ Cmap j) → (∀ j, 0 ≤ Cmetric j) →
    let Cpair := round3RepairClosedPairCost (m := m) (d := d) (N := N) Cs Cmap Cmetric
    let Cd := round3RepairClosedTensorCost (m := m) (d := d) (N := N) Cs Cmap Cmetric
    ∀ (budget epsilon eta : ℝ), 0 < budget → 0 < epsilon → 0 < eta →
    round3RepairReferenceLowBase packet+epsilon/4 ≤ budget/4 →
    let sigma := round3RepairClosedNumericalThreshold packet Cmap Cpair Cd budget epsilon eta k
    0 < sigma ∧ ∀ (t : ℝ) (ht : 0 < t) (htEntry : t ≤ sigma),
    ∀ (s : ℕ) (hks : k ≤ s), s ≤ k+1 →
    ∀ (state : Round3RepairClosedState packet budget epsilon eta k t),
    (packet.pairNorm state.map k t (40*(s+1))).toReal ≤ budget →
    ∀ (ht1 : t ≤ 1),
    let current := state.toSmoothingState s hk hks ht ht1
    ∀ (U : P × M → Ey),
    Round3ParameterJointIncrementConclusion Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      (current.smoothedMap packet) U (current.computedTarget packet) (40*(k+1)) (t^k)
      (t^(6/5 : ℝ)) (t^(11/10 : ℝ)) Cmap Cmetric →
    ∃ next : Round3RepairClosedState packet budget epsilon eta s (t^(6/5 : ℝ)),
      next.map = (fun z => state.map z+U z) ∧
      ∀ j, (packet.pairNorm next.map s (t^(6/5 : ℝ)) j).toReal ≤ budget/4+
        round3RepairClosedStateRate packet Cpair budget j*t^(1/5 : ℝ)*
          (1+(packet.pairNorm state.map k t j).toReal) := by
  obtain ⟨Cs,hCs,hNext⟩ := round3_repair_actual_closed_state_update packet hBS0 hTS0 hBP0 hTP0 hK k hk
  refine ⟨Cs,hCs,?_⟩
  intro Cmap Cmetric hCmap hCmetric Cpair Cd budget epsilon eta hbudget heps heta hFixed sigma
  have hCd (j : ℕ) : 0 ≤ Cd j := by
    exact add_nonneg (add_nonneg (hCmetric j) (hCs j))
      (mul_nonneg (mul_nonneg (actualRepairCrossCost_nonneg (m+1) d N j) (hCs j)) (hCmap j))
  have hCpair (j : ℕ) : 0 ≤ Cpair j := by
    exact add_nonneg (hCd j) (mul_nonneg (by positivity) (hCmap (j+1)))
  have hEntry := round3_repair_closed_numerical_threshold packet Cmap Cpair Cd hCmap hCpair hCd
    budget epsilon eta hbudget heps heta k
  refine ⟨hEntry.1,?_⟩
  intro t ht htEntry s hks hs state hExit ht1 current U hout
  have hTests := hEntry.2 t ht htEntry
  exact hNext Cmap Cmetric hCmap hCmetric budget epsilon eta heps.le hFixed t ht hTests.1 hTests.2.1
    s hks hs state hExit (hTests.2.2.1 s hks hs) hTests.2.2.2 U hout

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_closed_numerical_threshold
#print axioms GlobalEmbedding.Continuation.round3_repair_named_closed_state_update
