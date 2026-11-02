import Probes.Round3RepairConstructedBlock
import Probes.Round4ParameterStayBeforeMetric
import GlobalEmbedding.Offline.LeastFiniteBlockSchedule

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
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
local instance round4ParameterBlockChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round4ParameterBlockIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)








/-- Initial state plus genuine primitive mean/raw suppliers give the whole
finite block, including least waiting time and actual advancing map.  The
all-order recurrence is proved by the constructed same-U steps. -/
theorem round4Parameter_constructed_finite_block_before_metric [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ) (k : ℕ) (hk : 10 ≤ k)
    (cost : Round3RepairPrimitiveCosts)
    (budget epsilon eta : ℝ) (hbudget : 0 < budget) (heps : 0 < epsilon) (heta : 0 < eta)
    (hFixed : round3RepairReferenceLowBase packet+epsilon/4 ≤ budget/4) :
    ∃ (Cs : ℕ → ℝ) (sigma : ℝ),
    Cs = (fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j (40*(k+1))) ∧
    sigma = round4ParameterBlockScale packet Cs cost budget epsilon eta k ∧
    (∀ j, 0 ≤ Cs j) ∧ 0 < sigma ∧ sigma ≤ (1/2 : ℝ)^5 ∧
    sigma ≤ epsilon/(8*(cost.Cmap (k/2)+1)) ∧ sigma < cost.Theta^10 ∧
    let Cpair := round3RepairClosedPairCost (m := m) (d := d) (N := N) Cs cost.Cmap cost.Cmetric
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas
        packet.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i)),
    let changed := packet.withMetric metric hSym hSmooth
    ∀ (t : ℝ) (ht : 0 < t) (ht1 : t < 1), t ≤ sigma →
    ∀ (initial : Round3RepairClosedState changed budget epsilon eta k t),
    (∀ j, ∀ state : Round3RepairClosedState changed budget epsilon eta k (iterationScale t j),
      Nonempty (Round3RepairStatePrimitiveInput (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        changed cost state k hk le_rfl (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le)) →
    (∀ j, ∀ state : Round3RepairClosedState changed budget epsilon eta k (iterationScale t j),
      (changed.pairNorm state.map k (iterationScale t j) (40*(k+2))).toReal ≤ budget →
      Nonempty (Round3RepairStatePrimitiveInput (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        changed cost state (k+1) hk (Nat.le_succ k)
          (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le)) →
    ∀ (capNext : ℝ), 0 < capNext → ∀ (start : ℕ),
    Nonempty (Round3RepairConstructedBlock (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      changed cost Cpair budget epsilon eta k hk t ht ht1 initial capNext start) := by
  classical
  obtain ⟨Cs,sigma,hCsExact,hSigmaExact,hCs,hSigma,hSigmaSmall,hSigmaDisp,hSigmaTheta,hStay⟩ :=
    round4Parameter_constructed_stay_trajectory_before_metric (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet hBS0 hTS0 hBP0 hTP0 hK k hk cost budget epsilon eta hbudget heps heta hFixed
  refine ⟨Cs,sigma,hCsExact,hSigmaExact,hCs,hSigma,hSigmaSmall,hSigmaDisp,hSigmaTheta,?_⟩
  intro Cpair metric hSym hSmooth changed t ht ht1 htEntry initial supplyStay supplyAdvance capNext hcapNext start
  obtain ⟨states,hInitial,primitive,hUpdate,hOut,hRec,hAdvance⟩ :=
    hStay metric hSym hSmooth t ht ht1 htEntry initial supplyStay
  let Cd := round3RepairClosedTensorCost (m := m) (d := d) (N := N) Cs cost.Cmap cost.Cmetric
  have hCd (a : ℕ) : 0 ≤ Cd a := by
    exact add_nonneg (add_nonneg (cost.metric_nonneg a) (hCs a))
      (mul_nonneg (mul_nonneg (actualRepairCrossCost_nonneg (m+1) d N a) (hCs a)) (cost.map_nonneg a))
  have hCpair (a : ℕ) : 0 ≤ Cpair a :=
    add_nonneg (hCd a) (mul_nonneg (by positivity) (cost.map_nonneg (a+1)))
  have hRate (a : ℕ) : 0 ≤ round3RepairClosedStateRate changed Cpair budget a := by
    dsimp only [round3RepairClosedStateRate]
    exact add_nonneg (by positivity) (mul_nonneg (mul_nonneg (by norm_num) (hCpair a)) (by linarith))
  obtain ⟨J,hstart,hNorm,hPower,hLeast⟩ := exists_least_repair_norm_and_power_exit
    (ι := Unit) (κ := Unit)
    (fun _ j => (changed.pairNorm (states j).map k (iterationScale t j) (40*(k+2))).toReal)
    (fun _ => round3RepairClosedStateRate changed Cpair budget (40*(k+2)))
    (fun _ => 1) (fun _ => 1) (fun _ => capNext)
    ht ht1 (fun _ => hRate _) hbudget (fun _ => by norm_num) (fun _ => hcapNext)
    (fun _ => Filter.Eventually.of_forall fun j => hRec j (40*(k+2))) start
  have hNormJ := hNorm ()
  have hCapJ : iterationScale t J < capNext := by simpa only [Real.rpow_one,one_mul] using hPower ()
  have hExit : (changed.pairNorm (states J).map k (iterationScale t J) (40*(k+2))).toReal ≤ budget :=
    hNormJ.le.trans (by linarith)
  let advancing := Classical.choice (supplyAdvance J (states J) hExit)
  obtain ⟨next,hNext,hNextRec⟩ := hAdvance J hExit advancing
  have hScale := repair_step_scale_order (iterationScale_pos ht J) (iterationScale_lt_one ht.le ht1 J).le k hk
  refine ⟨{ states := states
            initial_map := hInitial
            primitive := primitive
            update := hUpdate
            recurrence := hRec
            waitIndex := J
            start_lt := hstart
            exit_norm := hNormJ
            exit_scale := hCapJ
            least := ?_
            advancing := advancing
            next := next
            next_map := hNext
            next_scale := (hScale.2.2.1.trans hScale.2.2.2).trans_lt hCapJ
            next_recurrence := hNextRec }⟩
  intro j hj hNormj hCapj
  exact hLeast j hj (fun _ => hNormj) (fun _ => by simpa only [Real.rpow_one,one_mul] using hCapj)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4Parameter_constructed_finite_block_before_metric
