import Probes.Round3RepairReferenceEnvelope

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
local instance round3RepairClosedUpdateChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairClosedUpdateIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)


/-- Fixed numerical coefficient in the actual full-pair recurrence. -/
def round3RepairClosedStateRate (Cpair : ℕ → ℝ) (budget : ℝ) (j : ℕ) : ℝ :=
  1+j*(paperAtlasCj j (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart Data.H)
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+
    2*Cpair j*(1+budget)

/-- Actual single-state closure.  Only finite numerical entrance tests and
the actual same-U conclusion are used; no next-map or next-error budget is
supplied.  The output retains every order, which is needed for finite waits. -/
theorem round3_repair_actual_closed_state_update [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ) (k : ℕ) (hk : 10 ≤ k) :
    ∃ Cs : ℕ → ℝ, (∀ j, 0 ≤ Cs j) ∧ ∀ (Cmap Cmetric : ℕ → ℝ),
    (∀ j, 0 ≤ Cmap j) → (∀ j, 0 ≤ Cmetric j) →
    let Cpair := round3RepairClosedPairCost (m := m) (d := d) (N := N) Cs Cmap Cmetric
    let Cd := round3RepairClosedTensorCost (m := m) (d := d) (N := N) Cs Cmap Cmetric
    ∀ (budget epsilon eta : ℝ), 0 ≤ epsilon →
    round3RepairReferenceLowBase packet+epsilon/4 ≤ budget/4 →
    ∀ (t : ℝ) (ht : 0 < t) (htsmall : t ≤ (1/2 : ℝ)^5),
    t ≤ epsilon/(8*(Cmap (k/2)+1)) →
    ∀ (s : ℕ) (hks : k ≤ s), s ≤ k+1 →
    ∀ (state : Round3RepairClosedState packet budget epsilon eta k t),
    (packet.pairNorm state.map k t (40*(s+1))).toReal ≤ budget →
    round3RepairClosedStateRate packet Cpair budget (40*(s+1))*t^(1/5 : ℝ)*(1+budget) ≤ 3*budget/4 →
    (2*Cd 0*(1+budget))*t^(1/5 : ℝ)*(1+budget) ≤ eta →
    let current := state.toSmoothingState s hk hks ht (by norm_num at htsmall; linarith)
    ∀ (U : P × M → Ey),
    Round3ParameterJointIncrementConclusion Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      (current.smoothedMap packet) U (current.computedTarget packet) (40*(k+1)) (t^k)
      (t^(6/5 : ℝ)) (t^(11/10 : ℝ)) Cmap Cmetric →
    ∃ next : Round3RepairClosedState packet budget epsilon eta s (t^(6/5 : ℝ)),
      next.map = (fun z => state.map z+U z) ∧
      ∀ j, (packet.pairNorm next.map s (t^(6/5 : ℝ)) j).toReal ≤ budget/4+
        round3RepairClosedStateRate packet Cpair budget j*t^(1/5 : ℝ)*
          (1+(packet.pairNorm state.map k t j).toReal) := by
  obtain ⟨Cs,hCs,hStep⟩ := round3_repair_closed_full_pair_and_defect_recurrence
    (m := m) (d := d) (N := N) (c := Data.parameterCount) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius k hk
  refine ⟨Cs,hCs,?_⟩
  intro Cmap Cmetric hCmap hCmetric Cpair Cd budget epsilon eta heps hFixed
    t ht htsmall hDisplacement s hks hs state hExit hPairSmall hDefectSmall current U hout
  obtain ⟨hCpair,hStep⟩ := hStep Cmap Cmetric hCmap hCmetric
  have ht1 : t ≤ 1 := by norm_num at htsmall; linarith
  have hbudget : 0 ≤ budget := ENNReal.toReal_nonneg.trans state.pair_budget
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hRef : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart Data.H i)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) := by
    rw [packet.reference_tensor]
    exact parameterRound2_inducedMetric_originalCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hRun := hStep Data.atlas packet.parameterFamily packet.domain.atlas_smooth hB
    packet.sourcePreparation (packet.closedParameterPreparation hK) packet.buffer packet.Omega packet.Q
    packet.source_compact packet.parameter_compact packet.source_target packet.parameter_target
    packet.source_sampling packet.parameter_sampling t ht ht1 s hs state.map state.smooth
    packet.metric Data.H packet.metric_smooth hRef budget state.pair_budget U hout
  have hBase := round3_repair_state_low_pair_base packet state ht.le heps hFixed
  have hAll (j : ℕ) :
      (packet.pairNorm (fun z => state.map z+U z) s (t^(6/5 : ℝ)) j).toReal ≤ budget/4+
        round3RepairClosedStateRate packet Cpair budget j*t^(1/5 : ℝ)*
          (1+(packet.pairNorm state.map k t j).toReal) := by
    exact ((hRun.2.2.2 j).1.2).trans (add_le_add hBase (le_refl _))
  have hRate (j : ℕ) : 0 ≤ round3RepairClosedStateRate packet Cpair budget j := by
    dsimp only [round3RepairClosedStateRate]
    exact add_nonneg (by positivity) (mul_nonneg (mul_nonneg (by norm_num) (hCpair j)) (by linarith))
  have hNextPair : (packet.pairNorm (fun z => state.map z+U z) s (t^(6/5 : ℝ)) (40*(s+1))).toReal ≤ budget := by
    have hMono := mul_le_mul_of_nonneg_left (add_le_add_left hExit 1)
      (mul_nonneg (hRate (40*(s+1))) (Real.rpow_nonneg ht.le (1/5 : ℝ)))
    linarith only [hAll (40*(s+1)),hMono,hPairSmall]
  have hZeroLe : packet.pairNorm state.map k t 0 ≤ packet.pairNorm state.map k t (40*(k+1)) := by
    unfold Round3RepairFixedSmoothingPacket.pairNorm parameterLocalOriginalTotalPairWeighted paperAtlasWeighted
    apply add_le_add <;> apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) <;>
      intro i hi hik <;> positivity
  have hZeroBudget : (packet.pairNorm state.map k t 0).toReal ≤ budget :=
    (ENNReal.toReal_mono (state.pairNorm_finite (40*(k+1))) hZeroLe).trans state.pair_budget
  have hCd : 0 ≤ Cd 0 := by
    dsimp only [Cd,round3RepairClosedTensorCost]
    exact add_nonneg (add_nonneg (hCmetric 0) (hCs 0))
      (mul_nonneg (mul_nonneg (actualRepairCrossCost_nonneg (m+1) d N 0) (hCs 0)) (hCmap 0))
  have hZeroSucc : 1+(packet.pairNorm state.map k t 0).toReal ≤ 1+budget := by linarith
  have hDMono := mul_le_mul_of_nonneg_left hZeroSucc
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCd) (show 0 ≤ 1+budget by linarith))
      (Real.rpow_nonneg ht.le (1/5 : ℝ)))
  have hD := (hRun.2.2.2 0).2.2
  simp only [paperAtlasWeighted,Finset.range_one,Finset.sum_singleton,pow_zero,one_mul,zero_add] at hD
  have hNextDefect : (packet.defectDistance (fun z => state.map z+U z) s (t^(6/5 : ℝ))).toReal ≤ eta :=
    hD.trans (hDMono.trans hDefectSmall)
  have hNextMap := round3_repair_same_increment_reference_envelope packet state hk ht htsmall heps
    (current.smoothedMap packet) U (current.computedTarget packet) (40*(k+1)) (t^(11/10 : ℝ))
    Cmap Cmetric hCmap hout hDisplacement
  refine ⟨{
    map := fun z => state.map z+U z
    smooth := hRun.1
    map_close := hNextMap
    defect_close := hNextDefect
    pair_budget := hNextPair }, rfl, hAll⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_actual_closed_state_update
