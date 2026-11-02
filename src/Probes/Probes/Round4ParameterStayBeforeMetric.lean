import Probes.Round4ParameterEntryBeforeMetric
import Probes.Round3RepairStatePrimitiveInput

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
local instance round4ParameterStayChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round4ParameterStayIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)







/-- A genuine fixed-stage trajectory from one initial state.  Every next map
is built by the literal mean-corrected sine/cosine formula and all budgets
are proved from the primitive raw witnesses.  No future state, U or output
estimate is assumed.  The numeric entrance precedes the initial map. -/
theorem round4Parameter_constructed_stay_trajectory_before_metric [CompactSpace M]
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
    ∃ states : ∀ j, Round3RepairClosedState changed budget epsilon eta k (iterationScale t j),
      (states 0).map = initial.map ∧
      ∃ primitive : ∀ j, Round3RepairStatePrimitiveInput (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        changed cost (states j) k hk le_rfl (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le,
      (∀ j, (states (j+1)).map = fun z => (states j).map z+(primitive j).increment changed z) ∧
      (∀ j, ∀ (htj : 0 < iterationScale t j) (htj1 : iterationScale t j ≤ 1),
        let current := (states j).toSmoothingState k hk le_rfl htj htj1
        Round3ParameterJointIncrementConclusion Data.atlas changed.parameterFamily.chart changed.closedSamples univ
          (current.smoothedMap changed) ((primitive j).increment changed) (current.computedTarget changed)
          (40*(k+1)) (iterationScale t j ^ k) ((iterationScale t j)^(6/5 : ℝ))
          ((iterationScale t j)^(11/10 : ℝ)) cost.Cmap cost.Cmetric) ∧
      (∀ j a, (changed.pairNorm (states (j+1)).map k (iterationScale t (j+1)) a).toReal ≤ budget/4+
        round3RepairClosedStateRate changed Cpair budget a*(iterationScale t j)^(1/5 : ℝ)*
          (1+(changed.pairNorm (states j).map k (iterationScale t j) a).toReal)) ∧
      ∀ j, (changed.pairNorm (states j).map k (iterationScale t j) (40*(k+2))).toReal ≤ budget →
      ∀ advancing : Round3RepairStatePrimitiveInput (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        changed cost (states j) (k+1) hk (Nat.le_succ k)
          (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le,
      ∃ next : Round3RepairClosedState changed budget epsilon eta (k+1) ((iterationScale t j)^(6/5 : ℝ)),
        next.map = (fun z => (states j).map z+advancing.increment changed z) ∧
        ∀ a, (changed.pairNorm next.map (k+1) ((iterationScale t j)^(6/5 : ℝ)) a).toReal ≤ budget/4+
          round3RepairClosedStateRate changed Cpair budget a*(iterationScale t j)^(1/5 : ℝ)*
            (1+(changed.pairNorm (states j).map k (iterationScale t j) a).toReal) := by
  classical
  let Cs := fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j (40*(k+1))
  obtain ⟨hCs,hNext⟩ := round4Parameter_named_closed_state_update_before_metric packet hBS0 hTS0 hBP0 hTP0 hK k hk
  let Cpair := round3RepairClosedPairCost (m := m) (d := d) (N := N) Cs cost.Cmap cost.Cmetric
  let Cd := round3RepairClosedTensorCost (m := m) (d := d) (N := N) Cs cost.Cmap cost.Cmetric
  let sigma0 := round3RepairClosedNumericalThreshold packet cost.Cmap Cpair Cd budget epsilon eta k
  obtain ⟨hSigma0,hNext⟩ := hNext cost.Cmap cost.Cmetric cost.map_nonneg cost.metric_nonneg
    budget epsilon eta hbudget heps heta hFixed
  let sigma := min sigma0 (cost.Theta^10/2)
  have hPow : 0 < cost.Theta^10 := pow_pos cost.theta_pos _
  have hSigma : 0 < sigma := lt_min hSigma0 (by positivity)
  have hSigmaHalf : sigma ≤ (1/2 : ℝ)^5 := (min_le_left _ _).trans (min_le_left _ _)
  have hSigmaDisp : sigma ≤ epsilon/(8*(cost.Cmap (k/2)+1)) := by
    apply le_trans (min_le_left _ _)
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hSigmaTheta : sigma < cost.Theta^10 := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨Cs,sigma,rfl,rfl,hCs,hSigma,hSigmaHalf,hSigmaDisp,hSigmaTheta,?_⟩
  intro CpairOut metric hSym hSmooth changed t ht ht1 htEntry initial supply
  have hNext := hNext metric hSym hSmooth
  have htjEntry (j : ℕ) : iterationScale t j ≤ sigma0 := by
    apply le_trans _ (htEntry.trans (min_le_left _ _))
    exact Real.rpow_le_self_of_le_one ht.le ht1.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 6/5))
  have htjTheta (j : ℕ) : iterationScale t j < cost.Theta^10 := by
    apply lt_of_le_of_lt _ (htEntry.trans_lt hSigmaTheta)
    exact Real.rpow_le_self_of_le_one ht.le ht1.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 6/5))
  let primitive (j : ℕ) (state : Round3RepairClosedState changed budget epsilon eta k (iterationScale t j)) :=
    Classical.choice (supply j state)
  have hout (j : ℕ) (state : Round3RepairClosedState changed budget epsilon eta k (iterationScale t j)) :=
    round3_repair_state_primitive_conclusion changed cost state k hk le_rfl
      (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le (primitive j state) (htjTheta j)
  have nextExists (j : ℕ) (state : Round3RepairClosedState changed budget epsilon eta k (iterationScale t j)) :=
    hNext (iterationScale t j) (iterationScale_pos ht j) (htjEntry j) k le_rfl (Nat.le_succ k)
      state state.pair_budget (iterationScale_lt_one ht.le ht1 j).le
      ((primitive j state).increment changed) (hout j state)
  let next (j : ℕ) (state : Round3RepairClosedState changed budget epsilon eta k (iterationScale t j)) :=
    Classical.choose (nextExists j state)
  let states : ∀ j, Round3RepairClosedState changed budget epsilon eta k (iterationScale t j) :=
    Nat.rec (initial.atEqualScale changed (by simp [iterationScale]))
      (fun j state => (next j state).atEqualScale changed (iterationScale_succ ht.le j).symm)
  have hsucc (j : ℕ) : (states (j+1)).map = (next j (states j)).map := by
    change ((next j (states j)).atEqualScale changed (iterationScale_succ ht.le j).symm).map = _
    exact Round3RepairClosedState.atEqualScale_map changed _ _
  refine ⟨states,?_,fun j => primitive j (states j),?_,?_,?_,?_⟩
  · change (initial.atEqualScale changed _).map = initial.map
    exact Round3RepairClosedState.atEqualScale_map changed _ _
  · intro j
    exact (hsucc j).trans (Classical.choose_spec (nextExists j (states j))).1
  · intro j htj htj1
    exact hout j (states j)
  · intro j a
    have h := (Classical.choose_spec (nextExists j (states j))).2 a
    rw [hsucc j,iterationScale_succ ht.le j]
    exact h
  · intro j hExit advancing
    have houtAdvance := round3_repair_state_primitive_conclusion changed cost (states j) (k+1) hk (Nat.le_succ k)
      (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le advancing (htjTheta j)
    exact hNext (iterationScale t j) (iterationScale_pos ht j) (htjEntry j) (k+1) (Nat.le_succ k) le_rfl
      (states j) hExit (iterationScale_lt_one ht.le ht1 j).le (advancing.increment changed) houtAdvance

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4Parameter_constructed_stay_trajectory_before_metric
