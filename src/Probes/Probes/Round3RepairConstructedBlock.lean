import Probes.Round3RepairConstructedStay
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
local instance round3RepairConstructedBlockChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairConstructedBlockIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)








/-- One actual finite repair block.  All intermediate maps come from their
recorded primitive mean/oscillation witnesses, and the terminal map is the
actual advancing sine/cosine update. -/
structure Round3RepairConstructedBlock [CompactSpace M]
    (cost : Round3RepairPrimitiveCosts) (Cpair : ℕ → ℝ)
    (budget epsilon eta : ℝ) (k : ℕ) (hk : 10 ≤ k)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (initial : Round3RepairClosedState packet budget epsilon eta k t)
    (capNext : ℝ) (start : ℕ) where
  states : ∀ j, Round3RepairClosedState packet budget epsilon eta k (iterationScale t j)
  initial_map : (states 0).map = initial.map
  primitive : ∀ j, Round3RepairStatePrimitiveInput (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet cost (states j) k hk le_rfl (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le
  update : ∀ j, (states (j+1)).map = fun z => (states j).map z+(primitive j).increment packet z
  recurrence : ∀ j a, (packet.pairNorm (states (j+1)).map k (iterationScale t (j+1)) a).toReal ≤ budget/4+
    round3RepairClosedStateRate packet Cpair budget a*(iterationScale t j)^(1/5 : ℝ)*
      (1+(packet.pairNorm (states j).map k (iterationScale t j) a).toReal)
  waitIndex : ℕ
  start_lt : start < waitIndex
  exit_norm : (packet.pairNorm (states waitIndex).map k (iterationScale t waitIndex) (40*(k+2))).toReal < budget/2
  exit_scale : iterationScale t waitIndex < capNext
  least : ∀ j, start < j →
    (packet.pairNorm (states j).map k (iterationScale t j) (40*(k+2))).toReal < budget/2 →
    iterationScale t j < capNext → waitIndex ≤ j
  advancing : Round3RepairStatePrimitiveInput (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet cost (states waitIndex) (k+1) hk (Nat.le_succ k)
      (iterationScale_pos ht waitIndex) (iterationScale_lt_one ht.le ht1 waitIndex).le
  next : Round3RepairClosedState packet budget epsilon eta (k+1) ((iterationScale t waitIndex)^(6/5 : ℝ))
  next_map : next.map = fun z => (states waitIndex).map z+advancing.increment packet z
  next_scale : (iterationScale t waitIndex)^(6/5 : ℝ) < capNext
  next_recurrence : ∀ a,
    (packet.pairNorm next.map (k+1) ((iterationScale t waitIndex)^(6/5 : ℝ)) a).toReal ≤ budget/4+
      round3RepairClosedStateRate packet Cpair budget a*(iterationScale t waitIndex)^(1/5 : ℝ)*
        (1+(packet.pairNorm (states waitIndex).map k (iterationScale t waitIndex) a).toReal)

/-- Initial state plus genuine primitive mean/raw suppliers give the whole
finite block, including least waiting time and actual advancing map.  The
all-order recurrence is proved by the constructed same-U steps. -/
theorem round3_repair_constructed_finite_block [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ) (k : ℕ) (hk : 10 ≤ k)
    (cost : Round3RepairPrimitiveCosts)
    (budget epsilon eta : ℝ) (hbudget : 0 < budget) (heps : 0 < epsilon) (heta : 0 < eta)
    (hFixed : round3RepairReferenceLowBase packet+epsilon/4 ≤ budget/4) :
    ∃ (Cs : ℕ → ℝ) (sigma : ℝ), (∀ j, 0 ≤ Cs j) ∧ 0 < sigma ∧ sigma ≤ (1/2 : ℝ)^5 ∧
    sigma ≤ epsilon/(8*(cost.Cmap (k/2)+1)) ∧ sigma < cost.Theta^10 ∧
    let Cpair := round3RepairClosedPairCost (m := m) (d := d) (N := N) Cs cost.Cmap cost.Cmetric
    ∀ (t : ℝ) (ht : 0 < t) (ht1 : t < 1), t ≤ sigma →
    ∀ (initial : Round3RepairClosedState packet budget epsilon eta k t),
    (∀ j, ∀ state : Round3RepairClosedState packet budget epsilon eta k (iterationScale t j),
      Nonempty (Round3RepairStatePrimitiveInput (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        packet cost state k hk le_rfl (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le)) →
    (∀ j, ∀ state : Round3RepairClosedState packet budget epsilon eta k (iterationScale t j),
      (packet.pairNorm state.map k (iterationScale t j) (40*(k+2))).toReal ≤ budget →
      Nonempty (Round3RepairStatePrimitiveInput (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        packet cost state (k+1) hk (Nat.le_succ k)
          (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le)) →
    ∀ (capNext : ℝ), 0 < capNext → ∀ (start : ℕ),
    Nonempty (Round3RepairConstructedBlock (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost Cpair budget epsilon eta k hk t ht ht1 initial capNext start) := by
  classical
  obtain ⟨Cs,sigma,hCs,hSigma,hSigmaSmall,hSigmaDisp,hSigmaTheta,hStay⟩ :=
    round3_repair_constructed_stay_trajectory (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet hBS0 hTS0 hBP0 hTP0 hK k hk cost budget epsilon eta hbudget heps heta hFixed
  refine ⟨Cs,sigma,hCs,hSigma,hSigmaSmall,hSigmaDisp,hSigmaTheta,?_⟩
  intro Cpair t ht ht1 htEntry initial supplyStay supplyAdvance capNext hcapNext start
  obtain ⟨states,hInitial,primitive,hUpdate,hOut,hRec,hAdvance⟩ :=
    hStay t ht ht1 htEntry initial supplyStay
  let Cd := round3RepairClosedTensorCost (m := m) (d := d) (N := N) Cs cost.Cmap cost.Cmetric
  have hCd (a : ℕ) : 0 ≤ Cd a := by
    exact add_nonneg (add_nonneg (cost.metric_nonneg a) (hCs a))
      (mul_nonneg (mul_nonneg (actualRepairCrossCost_nonneg (m+1) d N a) (hCs a)) (cost.map_nonneg a))
  have hCpair (a : ℕ) : 0 ≤ Cpair a :=
    add_nonneg (hCd a) (mul_nonneg (by positivity) (cost.map_nonneg (a+1)))
  have hRate (a : ℕ) : 0 ≤ round3RepairClosedStateRate packet Cpair budget a := by
    dsimp only [round3RepairClosedStateRate]
    exact add_nonneg (by positivity) (mul_nonneg (mul_nonneg (by norm_num) (hCpair a)) (by linarith))
  obtain ⟨J,hstart,hNorm,hPower,hLeast⟩ := exists_least_repair_norm_and_power_exit
    (ι := Unit) (κ := Unit)
    (fun _ j => (packet.pairNorm (states j).map k (iterationScale t j) (40*(k+2))).toReal)
    (fun _ => round3RepairClosedStateRate packet Cpair budget (40*(k+2)))
    (fun _ => 1) (fun _ => 1) (fun _ => capNext)
    ht ht1 (fun _ => hRate _) hbudget (fun _ => by norm_num) (fun _ => hcapNext)
    (fun _ => Filter.Eventually.of_forall fun j => hRec j (40*(k+2))) start
  have hNormJ := hNorm ()
  have hCapJ : iterationScale t J < capNext := by simpa only [Real.rpow_one,one_mul] using hPower ()
  have hExit : (packet.pairNorm (states J).map k (iterationScale t J) (40*(k+2))).toReal ≤ budget :=
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
#print axioms GlobalEmbedding.Continuation.round3_repair_constructed_finite_block
