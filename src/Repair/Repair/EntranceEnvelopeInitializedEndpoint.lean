import Repair.EntranceUniformLimitPhase
import Repair.EntranceReferenceEnvelopeCosts
import Repair.EntranceFromMapBounds
import Probes.Round4ParameterBlocksBeforeMetric
import Probes.Round4ParameterReservedBeforeMetric
import Probes.Round3RepairPhaseBeforeMetric
import Probes.Round3RepairPhaseMetricEndpoint
import Smoothing.Round3RepairInitialState

/-!
# Actual repair initialized at a previously fixed numerical entrance

The genuine reserved target and mean data use the compensated reference
budget. A positive entry chosen before the reference map, once proved no
larger than the actual block scale, supplies the literal initial map and
C440 target radius. No closed initial state or ideal update is supplied;
the same actual raw increments generate one smooth exact-metric limit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold Filter
open scoped Classical ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
universe uM uP uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
private local instance entranceEnvelopeInitializedChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance entranceEnvelopeInitializedIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
variable [T2Space M]

/-- One fixed reference packet selects every stage cost, geometric entrance,
the initial scale and target radius BEFORE the prescribed metric.  A C440
target and its genuine raw preparations then give the actual least-wait
trajectory and the same smooth exact-metric limit with full phase conditions. -/
theorem repairEntrance_envelope_initialized_endpoint_from_map_bounds [CompactSpace M]
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
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (primary : Round3ParameterWholePrimaryPieceSupply Data theta)
    (profiles : Round3ParameterWholeReferenceProfiles Data packet.domain hs theta primary)
    (hPrimaryParam : ∀ nu i a y, y ∈ tsupport (primary.piece nu i a).cutoff →
      y.1 ∈ Data.parameterNormDomain i.2)
    (secondary : Round3PreparedParameterSecondaryPacket Data packet.domain hs theta)
    (hSecondaryParam : ∀ r i a y, y ∈ (secondary.piece r i a).carrier →
      y.1 ∈ Data.parameterNormDomain i.2)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (cF cT MH : ℝ)
    (hcF : 0 < cF) (hcT : 0 < cT) (hMH : 0 ≤ MH)
    (hFirstValue : ∀ r i a, (secondary.piece r i a).cF = cF)
    (hFrameValue : ∀ r i a, (secondary.piece r i a).cT = cT)
    (hHessianBound : ∀ r i a, (secondary.piece r i a).MH ≤ MH)
    (hInverseBound : ∀ r i a j, 1 ≤ j → j ≤ 2 → (secondary.piece r i a).Tinv j ≤ T j)
    (R : ℕ) (hPart : ∀ z, ∑ i, theta i z = 1)
    (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ R)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (C2 C442 : ℝ) (hC2 : 0 ≤ C2) (hC442 : 0 ≤ C442)
    (hMap2 : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      packet.referenceMap) (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
      packet.closedSamples).toReal ≤ C2)
    (hMap442 : (paperAtlasCj 442 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      packet.referenceMap) (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
      packet.closedSamples).toReal ≤ C442)
    (envelope : ℕ → ℝ) (hEnvelope : ∀ j, packet.closedReferenceProfile j ≤ envelope j) :
    ∃ phaseEpsilon : ℝ, 0 < phaseEpsilon ∧
      phaseEpsilon = min
        (repairEntranceGeometryTolerance m d N profiles.Tinv profiles.cF profiles.cT profiles.MH
          profiles.cF_pos profiles.cT_pos)
        (repairEntranceGeometryTolerance m d N T cF cT MH hcF hcT) ∧
    ∀ (budget : ℝ) (hbudget : 0 < budget),
    ∃ Ctarget : ℕ → ℕ → ℝ, (∀ r j, 0 ≤ Ctarget r j) ∧
    (∀ r j, Ctarget r j = repairEntranceCompensatedTargetCost
      (fun a => round4SpatialPairConstant (m+1) d N radius hradius BS0 TS0 BP0 TP0 Ds Dp a (40*(10+r+1)))
      packet.closedReferenceProfile envelope budget j) ∧
    ∀ (profile : ℕ → Round3RepairPrimitiveProfiles)
      (epsilon eta : ℝ) (heps : 0 < epsilon) (heta : 0 < eta),
      epsilon ≤ phaseEpsilon →
      repairEntranceLowFromMap (m+1) d N C2+epsilon/4 ≤ budget/4 →
    ∃ cost : ℕ → Round3RepairPrimitiveCosts,
    (∀ r, Round4ParameterRepairCostIdentity.{uM,uP,uTr,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (fun j => Ctarget r j*budget+(j+1)*packet.closedReferenceProfile j)
      (40*(10+r+1)) (by omega) (profile r) (cost r)) ∧
    ∀ (cap : ℕ → ℝ), (∀ r, 0 < cap r) →
    ∃ (Cs : ℕ → ℕ → ℝ) (sigma : ℕ → ℝ),
    (∀ r, Cs r = (fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j (40*(10+r+1)))) ∧
    (∀ r, sigma r = min (round4ParameterBlockScale packet (Cs r) (cost r) budget epsilon eta (10+r)) (cap r/2)) ∧
    (∀ r j, 0 ≤ Cs r j) ∧ (∀ r, 0 < sigma r) ∧ (∀ r, sigma r ≤ (1/2 : ℝ)^5) ∧
    (∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1))) ∧
    (∀ r, sigma r < (cost r).Theta^10) ∧ (∀ r, sigma r < cap r) ∧
    ∀ (entry : ℝ), 0 < entry → entry ≤ sigma 0 →
    ∃ (t0 : ℝ) (ht0 : 0 < t0) (ht1 : t0 < 1), t0 ≤ sigma 0 ∧
    t0 = repairEntranceScale budget epsilon entry
      (repairEntranceLowFromMap (m+1) d N C2) (repairEntranceHighFromMap (m+1) d N C442) ∧
    ∃ targetRadius : ℝ, 0 < targetRadius ∧
    targetRadius = repairEntranceMetricRadius t0 budget eta ∧
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas
        packet.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i))
      (hPositive : ∀ p x, ∀ v : TangentSpace IT x, v ≠ 0 → 0 < metric p x v v),
    let changed := packet.withMetric metric hSym hSmooth
    ∃ reserved : ∀ r, Round3RepairReservedCosts (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      changed (profile r) (40*(10+r+1)) (by omega) budget,
    (∀ r, (reserved r).generated.targetCost=Ctarget r) ∧
    (∀ r, (reserved r).generated.cost=cost r) ∧
    ∀ (_hError : paperAtlasCj 440
      (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
        (fun p x => metric p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal targetRadius),
    (∀ (r : ℕ) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1), v ≤ sigma r →
      ∀ state : Round3RepairClosedState changed budget epsilon eta (10+r) v,
      ∀ (s : ℕ) (hks : 10+r ≤ s), s ≤ 10+r+1 →
      (changed.pairNorm state.map (10+r) v (40*(s+1))).toReal ≤ budget →
      Nonempty (Round3RepairRawIncrementWitness (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        changed (reserved r).generated.cost
        ((reserved r).generated.data (state.toSmoothingState s (Nat.le_add_right 10 r) hks hv hv1))
        (v^(1/10 : ℝ)) (v^(10+r)))) →
    ∃ initial : Round3RepairClosedState changed budget epsilon eta 10 t0,
      initial.map=(fun z => Real.sqrt (1-t0^20) • packet.referenceMap z) ∧
      (∀ p x, changed.normalizedDefect initial.map 10 t0 p x =
        Data.H p x+(t0^20)⁻¹ • (metric p x-Data.H p x)) ∧
      ∃ run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        changed cost Cs sigma budget epsilon eta t0 ht0 ht1 initial,
        Round3RepairPhaseMetricEndpoint changed run := by
  classical
  obtain ⟨phaseEpsilon,hPhase,hPhaseExact,hLimitPhase⟩ := repairEntrance_uniform_limit_phase_before_metric
    (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet hBS0 hTS0 hBP0 hTP0 hK hReference hOmega hQ hs hn
    theta primary profiles hPrimaryParam secondary hSecondaryParam T hT cF cT MH hcF hcT hMH
    hFirstValue hFrameValue hHessianBound hInverseBound R hPart hCount hSupport
  refine ⟨phaseEpsilon,hPhase,hPhaseExact,?_⟩
  intro budget hbudget
  have hCostFactory (r : ℕ) := repairEntrance_reserved_envelope_costs_before_metric
    (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet hBS0 hTS0 hBP0 hTP0 hK (40*(10+r+1)) (by omega) budget hbudget envelope hEnvelope
  let Ctarget := fun r => repairEntranceCompensatedTargetCost
    (fun j => round4SpatialPairConstant (m+1) d N radius hradius
      BS0 TS0 BP0 TP0 Ds Dp j (40*(10+r+1))) packet.closedReferenceProfile envelope budget
  have hCtarget : ∀ r j, 0 ≤ Ctarget r j := fun r => (hCostFactory r).1
  have hFactory (r : ℕ) := (hCostFactory r).2
  refine ⟨Ctarget,hCtarget,fun _ _ => rfl,?_⟩
  intro profile epsilon eta heps heta hPhaseSmall hFixed
  have hActualFixed : round3RepairReferenceLowBase packet+epsilon/4 ≤ budget/4 := by
    have hh := repairEntrance_reference_low_bound packet C2 hC2 hMap2
    linarith
  choose cost hIdentity hGetReserved using (fun r => hFactory r (profile r))
  have hNamed : ∀ r, Round4ParameterRepairCostIdentity.{uM,uP,uTr,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (fun j => Ctarget r j*budget+(j+1)*packet.closedReferenceProfile j)
      (40*(10+r+1)) (by omega) (profile r) (cost r) := by
    intro r
    have hProfile : (fun j => Ctarget r j*budget+(j+1)*packet.closedReferenceProfile j) =
        round4ParameterRepairReferenceProfile (m+1) d N radius hradius
          BS0 TS0 BP0 TP0 Ds Dp (40*(10+r+1)) envelope budget := by
      funext j
      exact repairEntranceCompensatedTargetCost_identity _ _ _ _ hbudget.ne' j
    rw [hProfile]
    exact hIdentity r
  refine ⟨cost,hNamed,?_⟩
  intro cap hCap
  obtain ⟨Cs,sigma,hCsExact,hSigmaExact,hCs,hSigma,hSmall,hDisp,hTheta,hCapSmall,hRun⟩ :=
    round4Parameter_constructed_capped_infinite_blocks_before_metric
      (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet hBS0 hTS0 hBP0 hTP0 hK cost budget epsilon eta hbudget heps heta hActualFixed cap hCap
  refine ⟨Cs,sigma,hCsExact,hSigmaExact,hCs,hSigma,hSmall,hDisp,hTheta,hCapSmall,?_⟩
  intro entry hEntry hEntryLe
  let t0 := repairEntranceScale budget epsilon entry
    (repairEntranceLowFromMap (m+1) d N C2) (repairEntranceHighFromMap (m+1) d N C442)
  let targetRadius := repairEntranceMetricRadius t0 budget eta
  obtain ⟨ht0,htHalf,htEntry,hRadius,hInitial⟩ :=
    repairEntrance_uniform_from_map_bounds budget epsilon eta entry C2 C442
      heps heta hEntry hC2 hC442 hFixed packet hMap2 hMap442
  have ht1 : t0 < 1 := htHalf.trans_lt (by norm_num)
  have htActualEntry : t0 ≤ sigma 0 := htEntry.trans hEntryLe
  refine ⟨t0,ht0,ht1,htActualEntry,rfl,targetRadius,hRadius,rfl,?_⟩
  intro metric hSym hSmooth hPositive changed
  choose reserved hTarget hCost using (fun r => hGetReserved r metric hSym hSmooth)
  refine ⟨reserved,hTarget,hCost,?_⟩
  intro hError supply
  obtain ⟨initial,hMap,hDefect⟩ := hInitial metric hSym hSmooth hError
  have hPrimitive : ∀ (r : ℕ) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1), v ≤ sigma r →
      ∀ state : Round3RepairClosedState changed budget epsilon eta (10+r) v,
      ∀ (s : ℕ) (hks : 10+r ≤ s), s ≤ 10+r+1 →
      (changed.pairNorm state.map (10+r) v (40*(s+1))).toReal ≤ budget →
      Nonempty (Round3RepairStatePrimitiveInput (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        changed (cost r) state s (Nat.le_add_right 10 r) hks hv hv1) := by
    intro r v hv hv1 hvEntry state s hks hsk hNorm
    obtain ⟨witness⟩ := supply r v hv hv1 hvEntry state s hks hsk hNorm
    have actual := witness.toPrimitive changed
    rw [hCost r] at actual
    exact ⟨actual⟩
  obtain ⟨run⟩ := hRun metric hSym hSmooth t0 ht0 ht1 htActualEntry initial hPrimitive
  have out : Round3RepairFullEndpoint changed run := {
    limit := run.full_metric_limit changed hK heps hSmall hDisp hTheta
    stages := run.full_stage_tendsto changed
    stage_step := run.full_stage_step changed
    actual_update := run.actual_update changed
    original_jets := run.full_original_derivative_convergence changed hK heps hSmall hDisp hTheta
    same_pair := run.full_joint_conclusion changed hTheta }
  refine ⟨initial,hMap,hDefect,run,?_⟩
  exact {
    smooth_metric := {
      full := out
      original_norms := run.full_original_norm_convergence changed hK heps hSmall hDisp hTheta
      immersion := out.actual_limit_original_immersion changed hPositive }
    phases := hLimitPhase metric hSym hSmooth run out hPhaseSmall }

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_envelope_initialized_endpoint_from_map_bounds
