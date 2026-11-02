import Probes.Round3RepairClosedNumericalEntry
import Probes.Round3RepairUpdateBeforeMetric

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
local instance round3RepairEntryBeforeMetricChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairEntryBeforeMetricIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)



/-- Named finite entrance applied immediately to the actual same-U update. -/
theorem round3_repair_named_closed_state_update_before_metric [CompactSpace M]
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
    0 < sigma ∧
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas
        packet.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i)),
    let changed := packet.withMetric metric hSym hSmooth
    ∀ (t : ℝ) (ht : 0 < t) (htEntry : t ≤ sigma),
    ∀ (s : ℕ) (hks : k ≤ s), s ≤ k+1 →
    ∀ (state : Round3RepairClosedState changed budget epsilon eta k t),
    (changed.pairNorm state.map k t (40*(s+1))).toReal ≤ budget →
    ∀ (ht1 : t ≤ 1),
    let current := state.toSmoothingState s hk hks ht ht1
    ∀ (U : P × M → Ey),
    Round3ParameterJointIncrementConclusion Data.atlas changed.parameterFamily.chart changed.closedSamples univ
      (current.smoothedMap changed) U (current.computedTarget changed) (40*(k+1)) (t^k)
      (t^(6/5 : ℝ)) (t^(11/10 : ℝ)) Cmap Cmetric →
    ∃ next : Round3RepairClosedState changed budget epsilon eta s (t^(6/5 : ℝ)),
      next.map = (fun z => state.map z+U z) ∧
      ∀ j, (changed.pairNorm next.map s (t^(6/5 : ℝ)) j).toReal ≤ budget/4+
        round3RepairClosedStateRate changed Cpair budget j*t^(1/5 : ℝ)*
          (1+(changed.pairNorm state.map k t j).toReal) := by
  obtain ⟨Cs,hCs,hNext⟩ := round3_repair_actual_closed_state_update_before_metric packet hBS0 hTS0 hBP0 hTP0 hK k hk
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
  intro metric hSym hSmooth changed t ht htEntry s hks hs state hExit ht1 current U hout
  have hTests := hEntry.2 t ht htEntry
  exact hNext metric hSym hSmooth Cmap Cmetric hCmap hCmetric budget epsilon eta heps.le hFixed t ht hTests.1 hTests.2.1
    s hks hs state hExit (hTests.2.2.1 s hks hs) hTests.2.2.2 U hout

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_named_closed_state_update_before_metric
