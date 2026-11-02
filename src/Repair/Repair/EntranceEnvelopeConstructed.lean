import Repair.EntranceUniformSecondaryEndpoint
import Repair.EntranceEnvelopeInitializedEndpoint
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators ENNReal
namespace GlobalEmbedding.Continuation
universe uM uP uΒ uSubSecondary uHost
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

private local instance literalRawSignedFinite (n : ℕ) :
    Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

/-- A single target-independent set of numerical choices and one actual
natural-time trajectory for each allowed target. It records the literal
initial map and defect, every original norm convergence, exact induced
metric, joint smoothness, immersion and original phase conditions through
the actual phase-metric endpoint of that same trajectory. -/
def RepairEnvelopeConstructedRepair
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (envelope : ℕ → ℝ) (entry fixedEpsilon fixedEta C2 C442 : ℝ) (Β : Type uΒ) (SubSecondary : Type uSubSecondary) [Fintype Β] [Fintype SubSecondary] (Lprimary : ℕ) (rho : ℝ) : Prop :=
    ∃ budget epsilon eta : ℝ, 0 < budget ∧ 0 < epsilon ∧ 0 < eta ∧ epsilon ≤ rho ∧
    epsilon = fixedEpsilon ∧ eta = fixedEta ∧
    budget = 4*(repairEntranceLowFromMap (m+1) d N C2+1) ∧
    ∃ (profile : ℕ → Round3RepairPrimitiveProfiles) (Ctarget : ℕ → ℕ → ℝ),
    (∀ r j, Ctarget r j = repairEntranceCompensatedTargetCost
      (fun a => round4SpatialPairConstant (m+1) d N radius hradius BS0 TS0 BP0 TP0 Ds Dp a (40*(10+r+1)))
      smoothing.closedReferenceProfile envelope budget j) ∧
    (∀ r, (profile r).Lprimary = Lprimary) ∧
    Round4ParameterSecondaryCompletedProfiles.{uM,uP,uΒ,0}
      (m := m) (d := d) (N := N) (M := M)
      radius hradius Ds Dp BS0 TS0 BP0 TP0 Given reference smoothing.closedReferenceProfile
      budget Lprimary Unit profile Ctarget ∧
    ∃ (cost : ℕ → Round3RepairPrimitiveCosts) (Cs : ℕ → ℕ → ℝ) (sigma : ℕ → ℝ),
      (∀ r, Round4ParameterRepairCostIdentity.{uM,uP,0,0,uΒ,uSubSecondary}
        (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
        (fun j => Ctarget r j*budget+(j+1)*smoothing.closedReferenceProfile j)
        (40*(10+r+1)) (by omega) (profile r) (cost r)) ∧
      (∀ r, Cs r = (fun j => round4PreparedPairConstant (m+1) d radius hradius
        BS0 TS0 BP0 TP0 Ds Dp j (40*(10+r+1)))) ∧
      ∃ cap : ℕ → ℝ, (∀ r, 0 < cap r) ∧
      (∃ geometryTolerance linearBound reserve : ℝ,
        0 < geometryTolerance ∧ 0 ≤ linearBound ∧ 0 < reserve ∧
        ∀ r, cap r = round3RepairComputedGeometryThreshold
          (2*round4PreparedPairConstant (m+1) d radius hradius
            BS0 TS0 BP0 TP0 Ds Dp 0 (40*(10+r+1)))
          budget (reference 0) linearBound reserve geometryTolerance) ∧
      (∀ r, sigma r = min (round4ParameterBlockScale smoothing (Cs r) (cost r)
        budget epsilon eta (10+r)) (cap r/2)) ∧
      (∀ r j, 0 ≤ Cs r j) ∧ (∀ r, 0 < sigma r) ∧
      (∀ r, sigma r ≤ (1/2 : ℝ)^5) ∧
      (∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1))) ∧
      (∀ r, sigma r < (cost r).Theta^10) ∧
    ∃ (t0 : ℝ) (ht0 : 0 < t0) (ht1 : t0 < 1), t0 ≤ sigma 0 ∧
    t0 = repairEntranceScale budget epsilon entry
      (repairEntranceLowFromMap (m+1) d N C2) (repairEntranceHighFromMap (m+1) d N C442) ∧
    ∃ targetRadius : ℝ, 0 < targetRadius ∧
    targetRadius = repairEntranceMetricRadius t0 budget eta ∧
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Ref.atlas
        smoothing.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart i))
      (hPositive : ∀ p x, ∀ v : TangentSpace 𝓙 x, v ≠ 0 → 0 < metric p x v v),
    paperAtlasCj 440 (incrementsOriginalTensorCoordinates Ref.atlas smoothing.parameterFamily.chart
      (fun p x => metric p x-Ref.H p x))
      (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart) smoothing.closedSamples ≤
        ENNReal.ofReal targetRadius →
    let changed := smoothing.withMetric metric hSym hSmooth
    ∃ initial : Round3RepairClosedState changed budget epsilon eta 10 t0,
      initial.map=(fun z => Real.sqrt (1-t0^20) • smoothing.referenceMap z) ∧
      (∀ p x, changed.normalizedDefect initial.map 10 t0 p x =
        Ref.H p x+(t0^20)⁻¹ • (metric p x-Ref.H p x)) ∧
      ∃ run : Round3RepairInfiniteBlocks (Tr := ℝ) (Λ := Fin Ref.primaryCount) (Β := Β)
        (SubSecondary := SubSecondary) changed cost Cs sigma budget epsilon eta t0 ht0 ht1 initial,
        Round3RepairPhaseMetricEndpoint changed run

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.RepairEnvelopeConstructedRepair
