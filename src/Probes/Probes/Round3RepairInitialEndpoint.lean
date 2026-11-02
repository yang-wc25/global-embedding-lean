import Probes.Round3RepairFullJoint

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold Filter
open scoped ContDiff ENNReal Topology
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
local instance round3RepairInitialEndpointChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairInitialEndpointIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)










/-- One terminal package for the actual full-time repair. Every displayed
map and tensor refers to the same literal U_j and the same physical Fstar. -/
structure Round3RepairFullEndpoint [CompactSpace M]
    {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
    {budget epsilon eta t : ℝ} {ht : 0 < t} {ht1 : t < 1}
    {initial : Round3RepairClosedState packet budget epsilon eta 10 t}
    (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost Cs sigma budget epsilon eta t ht ht1 initial) : Prop where
  limit : Round3RepairFullLimitConclusion packet run
  stages : Tendsto (run.stage packet) atTop atTop
  stage_step : ∀ j, run.stage packet (j+1)=run.stage packet j ∨
    run.stage packet (j+1)=run.stage packet j+1
  actual_update : ∀ j, (run.state packet (j+1)).map =
    fun z => (run.state packet j).map z+run.increment packet j z
  original_jets :
    let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
    ∀ i a y, y ∈ incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i →
      Tendsto (fun J => iteratedFDeriv ℝ a
        (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (run.state packet J).map i) y)
        atTop (𝓝 (iteratedFDeriv ℝ a
          (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart Fstar i) y))
  same_pair : ∀ j,
    let current := (run.state packet j).toSmoothingState (run.stage packet (j+1))
      (run.full_stage_ge_ten packet j) (run.full_stage_le_next packet j)
      (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le
    Round3ParameterJointIncrementConclusion Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      (current.smoothedMap packet) (run.increment packet j) (current.computedTarget packet)
      (40*(run.stage packet j+1)) (iterationScale t j^run.stage packet j)
      ((iterationScale t j)^(6/5 : ℝ)) ((iterationScale t j)^(11/10 : ℝ))
      (cost (run.level packet j)).Cmap (cost (run.level packet j)).Cmetric

/-- One actual initial state and primitive mean/raw data generate the full
coherent infinite repair at every natural time, its least finite waits,
and the exact-metric limit
with the original C2 reserve.  U, future states, output norm/error budgets,
scalar recurrences and terminal derivative convergence are not premises. -/
theorem round3_repair_initial_state_primitive_endpoint [CompactSpace M]
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
    ∃ run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost Cs sigma budget epsilon eta t ht ht1 initial,
      Round3RepairFullEndpoint packet run := by
  obtain ⟨Cs,sigma,hCs,hSigma,hSmall,hDisp,hTheta,hRun⟩ :=
    round3_repair_constructed_infinite_blocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet hBS0 hTS0 hBP0 hTP0 hK cost budget epsilon eta hbudget heps heta hFixed
  refine ⟨Cs,sigma,hCs,hSigma,hSmall,hDisp,hTheta,?_⟩
  intro t ht ht1 htEntry initial supply
  obtain ⟨run⟩ := hRun t ht ht1 htEntry initial supply
  exact ⟨run,{
    limit := run.full_metric_limit packet hK heps hSmall hDisp hTheta
    stages := run.full_stage_tendsto packet
    stage_step := run.full_stage_step packet
    actual_update := run.actual_update packet
    original_jets := run.full_original_derivative_convergence packet hK heps hSmall hDisp hTheta
    same_pair := run.full_joint_conclusion packet hTheta }⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_initial_state_primitive_endpoint
