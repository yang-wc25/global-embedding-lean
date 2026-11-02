import Repair.EntranceCanonicalFactoryPlanned
import Repair.EntrancePlannedNativePhaseRegular
import Repair.EndpointNativePhaseRegular

/-! The same actual limit has the repository's native PhaseRegular
predicate on every slice. The nonzero primary cutoff is obtained from
the real positive reference decomposition, not supplied as a cover. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation
universe uM uP
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

/-- Full original norms, one actual trajectory, exact metric, strict C2
closeness, and native phase regularity, all at the same fixed entrance. -/
def RepairEntranceCanonicalNativePlannedLimit
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS TS BP TP Ds Dp radius hradius reference Given)
    (p : RepairEntranceParameters) (fixed : RepairEntranceProfiles) (C2 C442 tolerance : ℝ) : Prop :=
  let budget := 4*(repairEntranceLowFromMap (m+1) d N C2+1)
  let t0 := repairEntranceScale budget p.epsilon
    (p.canonicalEntry.{uM,uP,0,0,0} (m := m) (d := d) (N := N) fixed)
    (repairEntranceLowFromMap (m+1) d N C2) (repairEntranceHighFromMap (m+1) d N C442)
  let targetRadius := repairEntranceMetricRadius t0 budget p.eta
  0 < t0 ∧ t0 < 1 ∧ 0 < targetRadius ∧
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
  ∃ (Fstar : P × M → Ey) (G u : ℕ → P × M → Ey) (stage : ℕ → ℕ),
    RepairOriginalNativeLimitConclusion Ref smoothing metric tolerance t0 Fstar G u stage

 theorem RepairEntranceCanonicalPlannedLimit.native
    {Ref : IncrementsOriginalNativeData (m+1) d N M P}
    {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    {smoothing : Round3RepairFixedSmoothingPacket Ref BS TS BP TP Ds Dp radius hradius reference Given}
    {p : RepairEntranceParameters} {fixed : RepairEntranceProfiles} {C2 C442 tolerance : ℝ}
    (h : RepairEntranceCanonicalPlannedLimit Ref smoothing p fixed C2 C442 tolerance)
    (hReferenceMap : Ref.F=smoothing.referenceMap) (hAll : Ref.parameterSet=univ)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Ref)
    (hImm : IncrementsOriginalSliceImmersionInputs Ref) :
    RepairEntranceCanonicalNativePlannedLimit Ref smoothing p fixed C2 C442 tolerance := by
  rcases h with ⟨ht0,ht1,hRadius,hFinish⟩
  refine ⟨ht0,ht1,hRadius,?_⟩
  intro metric hSym hSmooth hPositive hError
  obtain ⟨Fstar,G,u,stage,out⟩ := hFinish metric hSym hSmooth hPositive hError
  exact ⟨Fstar,G,u,stage,{
    toRepairOriginalLimitConclusion := out
    phase_regular := out.native_phase_regular hReferenceMap hAll hDecomp hImm }⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.RepairEntranceCanonicalPlannedLimit.native
