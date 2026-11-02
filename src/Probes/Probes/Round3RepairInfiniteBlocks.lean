import Probes.Round3RepairBlockDisplacement

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
local instance round3RepairInfiniteBlockChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairInfiniteBlockIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)










/-- A block entrance records its actual global microstep index.  Its defect
and map budgets are always computed from that same actual current map. -/
structure Round3RepairBlockEntry (budget epsilon eta : ℝ) (k : ℕ) (t sigma : ℝ) where
  index : ℕ
  admissible : iterationScale t index ≤ sigma
  state : Round3RepairClosedState packet budget epsilon eta k (iterationScale t index)

/-- One coherent infinite family of genuine least-wait blocks, with their
actual mean/oscillation witnesses retained.  The physical map at each next
entrance is the preceding block's actual advancing map. -/
structure Round3RepairInfiniteBlocks [CompactSpace M]
    (cost : ℕ → Round3RepairPrimitiveCosts) (Cs : ℕ → ℕ → ℝ) (sigma : ℕ → ℝ)
    (budget epsilon eta t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (initial : Round3RepairClosedState packet budget epsilon eta 10 t) where
  entry : ∀ r, Round3RepairBlockEntry packet budget epsilon eta (10+r) t (sigma r)
  initial_index : (entry 0).index = 0
  initial_map : (entry 0).state.map = initial.map
  block : ∀ r, Round3RepairConstructedBlock (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet (cost r) (round3RepairClosedPairCost (m := m) (d := d) (N := N) (Cs r) (cost r).Cmap (cost r).Cmetric)
    budget epsilon eta (10+r) (Nat.le_add_right 10 r)
    (iterationScale t (entry r).index) (iterationScale_pos ht _) (iterationScale_lt_one ht.le ht1 _)
    (entry r).state (sigma (r+1)/2) 0
  next_index : ∀ r, (entry (r+1)).index = (entry r).index+(block r).waitIndex+1
  next_map : ∀ r, (entry (r+1)).state.map = (block r).next.map

/-- All stage entrances are chosen before the initial map.  Primitive mean
and raw witnesses then recursively build the actual infinite repair blocks.
No sequence of future states or final increment/error budgets is assumed. -/
theorem round3_repair_constructed_infinite_blocks [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ)
    (cost : ℕ → Round3RepairPrimitiveCosts)
    (budget epsilon eta : ℝ) (hbudget : 0 < budget) (heps : 0 < epsilon) (heta : 0 < eta)
    (hFixed : round3RepairReferenceLowBase packet+epsilon/4 ≤ budget/4) :
    ∃ (Cs : ℕ → ℕ → ℝ) (sigma : ℕ → ℝ),
    (∀ r j, 0 ≤ Cs r j) ∧ (∀ r, 0 < sigma r) ∧ (∀ r, sigma r ≤ (1/2 : ℝ)^5) ∧
    (∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1))) ∧
    (∀ r, sigma r < (cost r).Theta^10) ∧
    ∀ (t : ℝ) (ht : 0 < t) (ht1 : t < 1), t ≤ sigma 0 →
    ∀ (initial : Round3RepairClosedState packet budget epsilon eta 10 t),
    (∀ (r : ℕ) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1), v ≤ sigma r →
      ∀ state : Round3RepairClosedState packet budget epsilon eta (10+r) v,
      ∀ (s : ℕ) (hks : 10+r ≤ s), s ≤ 10+r+1 →
      (packet.pairNorm state.map (10+r) v (40*(s+1))).toReal ≤ budget →
      Nonempty (Round3RepairStatePrimitiveInput (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        packet (cost r) state s (Nat.le_add_right 10 r) hks hv hv1)) →
    Nonempty (Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost Cs sigma budget epsilon eta t ht ht1 initial) := by
  classical
  have hStage (r : ℕ) := round3_repair_constructed_finite_block (Tr := Tr) (Λ := Λ) (Β := Β)
    (SubSecondary := SubSecondary) packet hBS0 hTS0 hBP0 hTP0 hK (10+r) (Nat.le_add_right 10 r)
    (cost r) budget epsilon eta hbudget heps heta hFixed
  choose Cs sigma hCs hSigma hSmall hDisp hTheta hBlock using hStage
  refine ⟨Cs,sigma,hCs,hSigma,hSmall,hDisp,hTheta,?_⟩
  intro t ht ht1 htEntry initial supply
  have blockExists (r : ℕ) (entry : Round3RepairBlockEntry packet budget epsilon eta (10+r) t (sigma r)) :=
    hBlock r (iterationScale t entry.index) (iterationScale_pos ht _) (iterationScale_lt_one ht.le ht1 _)
      entry.admissible entry.state
      (fun j state => supply r (iterationScale (iterationScale t entry.index) j)
        (iterationScale_pos (iterationScale_pos ht _) _) (iterationScale_lt_one (iterationScale_pos ht _).le
          (iterationScale_lt_one ht.le ht1 _) _).le
        ((Real.rpow_le_self_of_le_one (iterationScale_pos ht _).le (iterationScale_lt_one ht.le ht1 _).le
          (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 6/5))).trans entry.admissible)
        state (10+r) le_rfl (Nat.le_succ _) state.pair_budget)
      (fun j state hExit => supply r (iterationScale (iterationScale t entry.index) j)
        (iterationScale_pos (iterationScale_pos ht _) _) (iterationScale_lt_one (iterationScale_pos ht _).le
          (iterationScale_lt_one ht.le ht1 _) _).le
        ((Real.rpow_le_self_of_le_one (iterationScale_pos ht _).le (iterationScale_lt_one ht.le ht1 _).le
          (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 6/5))).trans entry.admissible)
        state (10+r+1) (Nat.le_succ _) le_rfl hExit)
      (sigma (r+1)/2) (div_pos (hSigma (r+1)) (by norm_num)) 0
  let block (r : ℕ) (entry : Round3RepairBlockEntry packet budget epsilon eta (10+r) t (sigma r)) :=
    Classical.choice (blockExists r entry)
  have hScale (r : ℕ) (entry : Round3RepairBlockEntry packet budget epsilon eta (10+r) t (sigma r)) :
      (iterationScale (iterationScale t entry.index) (block r entry).waitIndex)^(6/5 : ℝ) =
        iterationScale t (entry.index+(block r entry).waitIndex+1) := by
    rw [← iterationScale_succ (iterationScale_pos ht _).le]
    rw [← iterationScale_add ht.le]
    simp only [Nat.add_assoc]
  let next (r : ℕ) (entry : Round3RepairBlockEntry packet budget epsilon eta (10+r) t (sigma r)) :
      Round3RepairBlockEntry packet budget epsilon eta (10+(r+1)) t (sigma (r+1)) :=
    { index := entry.index+(block r entry).waitIndex+1
      admissible := by
        rw [← hScale r entry]
        exact (block r entry).next_scale.le.trans (by have := hSigma (r+1); linarith)
      state := (block r entry).next.atEqualScale packet (hScale r entry) }
  let entry : ∀ r, Round3RepairBlockEntry packet budget epsilon eta (10+r) t (sigma r) :=
    Nat.rec { index := 0
              admissible := by simpa using htEntry
              state := initial.atEqualScale packet (by simp) }
      (fun r state => next r state)
  refine ⟨{ entry := entry
            initial_index := rfl
            initial_map := ?_
            block := fun r => block r (entry r)
            next_index := fun r => rfl
            next_map := ?_ }⟩
  · exact Round3RepairClosedState.atEqualScale_map packet initial _
  · intro r
    exact Round3RepairClosedState.atEqualScale_map packet (block r (entry r)).next _

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_constructed_infinite_blocks
