import Probes.Round3RepairLimitPhase

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
local instance round3RepairPhaseMetricEndpointChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairPhaseMetricEndpointIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)










variable [T2Space M]

/-- The actual natural-time repair with its same global metric limit,
original every-order convergence and all original phase conditions. -/
structure Round3RepairPhaseMetricEndpoint [CompactSpace M]
    {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
    {budget epsilon eta t : ℝ} {ht : 0 < t} {ht1 : t < 1}
    {initial : Round3RepairClosedState packet budget epsilon eta 10 t}
    (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost Cs sigma budget epsilon eta t ht ht1 initial) : Prop where
  smooth_metric : Round3RepairSmoothMetricEndpoint packet run
  phases : Round3RepairActualLimitPhase packet run

/-- A fixed original phase tolerance is chosen first. From one actual
initial state and true raw mean/secondary data, the literal SF/SH and U_j
construction then produces the full infinite repair and its one exact
metric, jointly smooth, phase-regular limit. The raw geometric supplier is
explicit; it contains no U, error budget, future state or convergence input. -/
theorem round3_repair_initial_raw_phase_metric_endpoint [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ)
    (hReference : packet.referenceMap = Data.F)
    (hOmega : Data.sourceNormDomain = packet.Omega)
    (hQ : Data.parameterNormDomain = packet.Q)
    (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data packet.domain hs)
    (hn : IncrementsOriginalFreeNormalConditions Data packet.domain hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hPositive : ∀ p x, ∀ v : TangentSpace IT x, v ≠ 0 → 0 < packet.metric p x v v) :
    ∃ phaseEpsilon : ℝ, 0 < phaseEpsilon ∧
    ∀ (profile : ℕ → Round3RepairPrimitiveProfiles)
      (budget epsilon eta : ℝ) (hbudget : 0 < budget) (heps : 0 < epsilon) (heta : 0 < eta),
      epsilon ≤ phaseEpsilon →
      round3RepairReferenceLowBase packet+epsilon/4 ≤ budget/4 →
    ∃ generated : ∀ r, Round3RepairGeneratedCosts (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet (profile r) (40*(10+r+1)) (by omega) budget,
    let cost := fun r => (generated r).cost
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
      Nonempty (Round3RepairRawIncrementWitness (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        packet (cost r)
        ((generated r).data (state.toSmoothingState s (Nat.le_add_right 10 r) hks hv hv1))
        (v^(1/10 : ℝ)) (v^(10+r)))) →
    ∃ run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost Cs sigma budget epsilon eta t ht ht1 initial,
      Round3RepairPhaseMetricEndpoint packet run := by
  obtain ⟨phaseEpsilon,hPhase,hLimitPhase⟩ := round3_repair_actual_limit_phase_tolerance
    (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet hBS0 hTS0 hBP0 hTP0 hK hReference hOmega hQ hs hp hn hImm
  refine ⟨phaseEpsilon,hPhase,?_⟩
  intro profile budget epsilon eta hbudget heps heta hPhaseSmall hFixed
  obtain ⟨generated,Cs,sigma,hCs,hSigma,hSmall,hDisp,hTheta,hRun⟩ :=
    round3_repair_initial_raw_smooth_metric_endpoint (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet hBS0 hTS0 hBP0 hTP0 hK profile budget epsilon eta hbudget heps heta hFixed hPositive
  refine ⟨generated,Cs,sigma,hCs,hSigma,hSmall,hDisp,hTheta,?_⟩
  intro t ht ht1 htEntry initial supply
  obtain ⟨run,out⟩ := hRun t ht ht1 htEntry initial supply
  exact ⟨run,⟨out,hLimitPhase run out.full hPhaseSmall⟩⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_initial_raw_phase_metric_endpoint
