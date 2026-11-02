import Repair.EntranceFactoryAssembly
import Repair.EntranceFinitePlanActualEndpoint
import Repair.EntranceEnvelopePublic

/-! The full original conclusion at an already fixed numerical entrance.
This connector consumes the certificate manufactured by the actual two
factories; the next public theorem constructs that certificate internally. -/
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
private local instance (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

/-- No trajectory or output is assumed: this is precisely the final
existence assertion, at the explicit entrance fixed by `p` and `fixed`. -/
def RepairEntrancePlannedLimit
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS TS BP TP Ds Dp radius hradius reference Given)
    (p : RepairEntranceParameters) (fixed : RepairEntranceProfiles) (C2 C442 tolerance : ℝ) : Prop :=
  let budget := 4*(repairEntranceLowFromMap (m+1) d N C2+1)
  let t0 := repairEntranceScale budget p.epsilon
    (p.entry.{uM,uP,0,0,0} (m := m) (d := d) (N := N) (M := M) fixed)
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
    RepairOriginalLimitConclusion Ref smoothing metric tolerance t0 Fstar G u stage

 theorem repairEntrance_factory_assembled_planned_limit
    (fixed : RepairEntranceProfiles)
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (reference Given : ℕ → ℝ)
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS TS BP TP Ds Dp radius hradius reference Given)
    (hReferenceMap : Ref.F=smoothing.referenceMap)
    (hNormSource : Ref.sourceNormDomain=smoothing.Omega)
    (hNormParameter : Ref.parameterNormDomain=smoothing.Q)
    (hAll : Ref.parameterSet=univ)
    (hs : IncrementsOriginalSmoothInputs Ref)
    (hp : IncrementsOriginalPhaseConditions Ref smoothing.domain hs)
    (hn : IncrementsOriginalFreeNormalConditions Ref smoothing.domain hs)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Ref)
    (hLinear : IncrementsOriginalLinearSmoothInputs Ref)
    (Lprimary : ℕ)
    (hLocal : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Ref.cutoff nu))).card ≤ Lprimary)
    (hImm : IncrementsOriginalSliceImmersionInputs Ref)
    (lower : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (rhoReserve : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Ref rhoReserve)
    (tolerance : ℝ) (hTolerance : 0 < tolerance)
    (C2 C442 : ℝ) (hC2 : 0 ≤ C2) (hC442 : 0 ≤ C442)
    (hMap2 : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
      smoothing.referenceMap) (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
      smoothing.closedSamples).toReal ≤ C2)
    (hMap442 : (paperAtlasCj 442 (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
      smoothing.referenceMap) (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
      smoothing.closedSamples).toReal ≤ C442)
    (envelope : ℕ → ℝ) (hEnvelope : ∀ j, smoothing.closedReferenceProfile j ≤ envelope j)
    (primaryNumbers secondaryNumbers : RepairEntranceFrameNumbers m d N)
    (FC IC MC SF SI : ℕ → ℝ)
    (SC : (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℕ → ℕ → ℝ) :
    let theta := round3ParameterProductParent Ref.atlas smoothing.parameterFamily
      (squareNormalizedCutoff smoothing.sourcePreparation.raw)
      (tensorLocalNormalizedCutoff smoothing.parameterPreparation.raw)
    ∀ (a : RepairEntranceFactoryAssembly Ref smoothing.domain hs hn theta
      primaryNumbers secondaryNumbers FC IC MC SF SI SC)
      (hPart : ∀ z, ∑ i, theta i z=1)
      (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1))
      (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M)),
    let phaseTolerance := min primaryNumbers.tolerance secondaryNumbers.tolerance
    let geometryTolerance := min primaryNumbers.tolerance
      (min secondaryNumbers.tolerance (incrementOriginalEllipticityTolerance (m+1) d N lower))
    let parameters := repairEntranceSelectedParameters m d N Ds Dp Lprimary radius hradius
      primaryNumbers.cF primaryNumbers.cT secondaryNumbers.cT lower rhoReserve C2 (fixed.Given 0)
      phaseTolerance geometryTolerance tolerance hReserve.reserve_pos hC2
      (lt_min primaryNumbers.tolerance_pos secondaryNumbers.tolerance_pos)
      (lt_min primaryNumbers.tolerance_pos (lt_min secondaryNumbers.tolerance_pos
        (incrementOriginalEllipticityTolerance_pos (m+1) d N lower hEll.lower_pos))) hTolerance
    let actual := repairEntranceSelectedProfiles BS TS BP TP IC FC Given reference envelope MC
      (SC BS TS BP TP Ds Dp) SI SF hBS hTS hBP hTP
      (fun j => ENNReal.toReal_nonneg.trans (smoothing.reference_bound j))
      (fun j => ENNReal.toReal_nonneg.trans (hEnvelope j))
    fixed.Prefix actual repairEntrancePrimitiveDepth →
    RepairEntrancePlannedLimit Ref smoothing parameters fixed C2 C442 tolerance := by
  intro theta a hPart hCount hSupport phaseTolerance geometryTolerance parameters actual hPrefix
  have hGiven0 : Given 0=fixed.Given 0 := (hPrefix.Given 0 (by omega)).symm
  have hRun := repairEntrance_actual_finite_plan_repair_endpoint fixed Ref BS TS BP TP hBS hTS hBP hTP
    Ds Dp radius hradius reference Given smoothing hReferenceMap hNormSource hNormParameter hAll
    hs hp hn hDecomp hLinear Lprimary hLocal hImm lower hEll rhoReserve hReserve tolerance hTolerance
    C2 C442 hC2 hC442 hMap2 hMap442 envelope hEnvelope
    a.primary a.profiles a.observer MC a.meta_nonneg a.cutoff a.primary_parameter
    a.secondary hPart hCount hSupport a.secondary_parameter a.numeric a.charts
  simp only [a.primary_tolerance,a.secondary_tolerance] at hRun
  simp only [a.primary_cF,a.primary_cT,a.secondary_cT,
    a.primary_forward,a.primary_observer_inverse,a.secondary_forward,a.secondary_observer_inverse,
    a.secondary_cutoff,hGiven0] at hRun
  have hActual : RepairEnvelopeConstructedRepair Ref smoothing envelope
      (parameters.entry.{uM,uP,0,0,0} (m := m) (d := d) (N := N) (M := M) fixed)
      parameters.epsilon parameters.eta C2 C442
      (Round3ParameterWholePrimaryIndex Ref theta a.primary)
      (Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hs theta a.secondary)
      Lprimary tolerance := hRun hPrefix
  obtain ⟨t0,targetRadius,ht0,ht1,hRadius,hTExact,hRadiusExact,hFinish⟩ :=
    hActual.original_conclusion Ref smoothing hReferenceMap envelope
      (parameters.entry.{uM,uP,0,0,0} (m := m) (d := d) (N := N) (M := M) fixed)
      parameters.epsilon parameters.eta C2 C442 _ _ Lprimary tolerance
  subst t0
  subst targetRadius
  exact ⟨ht0,ht1,hRadius,hFinish⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_factory_assembled_planned_limit
