import Smoothing.Round3OuterLiteralRawBeforeMetric
import Probes.Round3PreparedReferenceInputProfile
import Probes.Round3PreparedLiteralClosedRawStep
import Probes.Round3RepairEndpointBeforeMetric
import Probes.Round3ParameterActualCoherentConclusionRepair
import Smoothing.Round3RepairLiteralStage
import Smoothing.Round3OuterComputedStageOriginalInputs

/-! The complete actual fixed-reference repair construction. The original
reference assumptions manufacture the geometric packets, numerical profiles,
all stage caps, the literal (6.9) initial state and every raw increment used
by the same least-wait trajectory. All these choices precede the target
metric. No initial state, raw supplier, future state, output estimate or
convergence assertion is an input. This is a fixed-reference closed-sample
endpoint; the frozen source-equivalence and uniform finite-reference-order
acceptance remain separate requirements. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
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
def Round3OuterConstructedRepair
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (Β SubSecondary : Type*) [Fintype Β] [Fintype SubSecondary] (rho : ℝ) : Prop :=
    ∃ budget epsilon eta : ℝ, 0 < budget ∧ 0 < epsilon ∧ 0 < eta ∧ epsilon ≤ rho ∧
    ∃ (cost : ℕ → Round3RepairPrimitiveCosts) (Cs : ℕ → ℕ → ℝ) (sigma : ℕ → ℝ),
      (∀ r j, 0 ≤ Cs r j) ∧ (∀ r, 0 < sigma r) ∧
      (∀ r, sigma r ≤ (1/2 : ℝ)^5) ∧
      (∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1))) ∧
      (∀ r, sigma r < (cost r).Theta^10) ∧
    ∃ (t0 : ℝ) (ht0 : 0 < t0) (ht1 : t0 < 1), t0 ≤ sigma 0 ∧
    ∃ targetRadius : ℝ, 0 < targetRadius ∧
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

theorem round3_actual_original_constructed_repair_endpoint
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (reference Given : ℕ → ℝ)
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (hReferenceMap : Ref.F = smoothing.referenceMap)
    (hNormSource : Ref.sourceNormDomain = smoothing.Omega)
    (hNormParameter : Ref.parameterNormDomain = smoothing.Q)
    (hAll : Ref.parameterSet = univ)
    (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hpRef : IncrementsOriginalPhaseConditions Ref smoothing.domain hsRef)
    (hnRef : IncrementsOriginalFreeNormalConditions Ref smoothing.domain hsRef)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Ref)
    (hLinear : IncrementsOriginalLinearSmoothInputs Ref)
    (hImmRef : IncrementsOriginalSliceImmersionInputs Ref)
    (lower : ℝ) (hEllRef : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Ref rho)
    (tolerance : ℝ) (hTolerance : 0 < tolerance) :
    let theta := round3ParameterProductParent Ref.atlas smoothing.parameterFamily
      (squareNormalizedCutoff smoothing.sourcePreparation.raw)
      (tensorLocalNormalizedCutoff smoothing.parameterPreparation.raw)
    ∃ (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref smoothing.domain hsRef theta packet)
      (secondary : Round3PreparedParameterSecondaryPacket Ref smoothing.domain hsRef theta),
      Round3OuterConstructedRepair Ref smoothing
        (Round3ParameterWholePrimaryIndex Ref theta packet)
        (Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hsRef theta secondary) tolerance := by
  classical
  intro theta
  let base := round3RepairReferenceLowBase smoothing
  have hbase : 0 ≤ base := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  let budget := 4*(base+1)
  have hbudget : 0 < budget := by dsimp only [budget]; positivity
  let ML := max base (Given 0)
  have hML0 : 0 ≤ ML := hbase.trans (le_max_left _ _)
  have hRefProfile := round3_prepared_actual_reference_linear_profile Ref smoothing
    hReferenceMap hAll hNormSource hNormParameter
  obtain ⟨packet,profiles,secondary,hPart,hCount,hSupport,epsilonGeom,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
      hEpsilonGeom,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,hByOrder⟩ :=
    round3_actual_original_literal_raw_before_metric Ref BS0 TS0 BP0 TP0
      hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius reference Given smoothing
      hReferenceMap hNormSource hNormParameter hAll hsRef hpRef hnRef hDecomp hLinear hImmRef
      lower hEllRef rho hReserve budget ML hbudget.le hRefProfile.1 hRefProfile.2
  let Β := Round3ParameterWholePrimaryIndex Ref theta packet
  let Sub := Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hsRef theta secondary
  obtain ⟨phaseEpsilon,hPhase,hEndpoint⟩ := round3_repair_initialized_endpoint_before_metric
    (Tr := ℝ) (Λ := Fin Ref.primaryCount) (Β := Β) (SubSecondary := Sub)
    smoothing hBS0 hTS0 hBP0 hTP0 hAll hReferenceMap.symm hNormSource hNormParameter
      hsRef hpRef hnRef hImmRef
  obtain ⟨CtargetReserved,hCtargetReserved,hWithProfile⟩ := hEndpoint budget hbudget
  choose Cnormal hCnormal Cmap hCmap CtargetStage hCtargetStage Mrest Cut hMrest hCut
    CsGeom hCsGeom hSigmaGeom hPacket hRaw using (fun r => hByOrder (10+r) (Nat.le_add_right 10 r))
  let Packet := fun r j => max (Cmap r j*budget)
    (max (CtargetStage r j*budget+(j+1)*reference j) (max (Given j) (Cnormal r j)))
  let profile := fun r => round3OuterLiteralRawProfile Ref smoothing hsRef theta packet profiles
    (40*(10+r+1)) (by omega) budget lower (rho/4) (div_pos hReserve.reserve_pos (by norm_num))
    (Packet r) ForwardC InverseC MetaC (hPacket r) (CtargetReserved r) (Mrest r) (Cut r) Tinv Tobs
  let epsilon := min 1 (min phaseEpsilon (min epsilonGeom tolerance))
  have hepsilon : 0 < epsilon := lt_min (by norm_num) (lt_min hPhase (lt_min hEpsilonGeom hTolerance))
  have hEpsOne : epsilon ≤ 1 := min_le_left _ _
  have hEpsPhase : epsilon ≤ phaseEpsilon := (min_le_right _ _).trans (min_le_left _ _)
  have hEpsGeom : epsilon ≤ epsilonGeom :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hEpsTolerance : epsilon ≤ tolerance :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let L := ‖actualOriginalCoefficientFunctional (m+1)‖*ML
  have hL : 0 ≤ L := mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hML0
  let eta := rho/(4*(L+1))
  have heta : 0 < eta := div_pos hReserve.reserve_pos (by positivity)
  have hFixed : round3RepairReferenceLowBase smoothing+epsilon/4 ≤ budget/4 := by
    change base+epsilon/4 ≤ (4*(base+1))/4
    linarith
  let cap := fun r => round3RepairComputedGeometryThreshold (CsGeom r) budget (reference 0) L rho epsilonGeom
  have hCap : ∀ r, 0 < cap r := hSigmaGeom
  obtain ⟨cost,hWithCap⟩ := hWithProfile profile epsilon eta hepsilon heta hEpsPhase hFixed
  obtain ⟨Cs,sigma,hCs,hSigma,hSmall,hDisp,hTheta,hCapSmall,t0,ht0,ht1,htEntry,targetRadius,hRadius,hFinish⟩ :=
    hWithCap cap hCap
  refine ⟨packet,profiles,secondary,budget,epsilon,eta,hbudget,hepsilon,heta,hEpsTolerance,
    cost,Cs,sigma,hCs,hSigma,hSmall,hDisp,hTheta,t0,ht0,ht1,htEntry,targetRadius,hRadius,?_⟩
  intro metric hSym hSmooth hPositive hError changed
  obtain ⟨reserved,hTarget,hCost,hRun⟩ := hFinish metric hSym hSmooth hPositive
  apply hRun hError
  intro r v hv hv1 hvEntry state s hks hsk hNorm
  have hvCap : v ≤ cap r := hvEntry.trans (hCapSmall r).le
  have hvTheta : v < (reserved r).generated.cost.Theta^10 := by
    rw [hCost r]
    exact hvEntry.trans_lt (hTheta r)
  exact round3_prepared_literal_closed_raw_step Ref changed hsRef hAll hNormSource hNormParameter theta packet profiles secondary
    (10+r) (Nat.le_add_right 10 r) budget ML lower rho hReserve.reserve_pos epsilonGeom (CsGeom r)
    (Packet r) ForwardC InverseC MetaC (Mrest r) (Cut r) Tinv Tobs (hPacket r)
    (hRaw r metric hSym hSmooth)
    (CtargetReserved r) (reserved r) (hTarget r) epsilon eta v hepsilon.le hEpsGeom le_rfl
    hv hv1 hvCap hvTheta state s hks

#print axioms round3_actual_original_constructed_repair_endpoint
end GlobalEmbedding.Continuation
