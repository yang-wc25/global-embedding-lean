import Repair.EntranceEnvelopeInitializedEndpoint
import Repair.EntranceEnvelopeConstructed
import Repair.EntranceSelectedNumericalParameters
import Repair.EntranceUniformSecondaryEndpoint
import Repair.IncrementDirectNumericalLiteralRaw

/-!
# The actual full repair uses a fixed finite numerical plan

The literal primary, mean, solver and secondary factory is connected to
compensated reference budgets, the prescribed finite-plan entrance, the
actual initial map and defect, one natural-time trajectory, and the same
smooth exact-metric phase limit. A matching finite prefix of the primitive
input budgets is the only comparison with the fixed numerical plan; no
initial state, ideal step or output estimate is supplied. Producing this
prefix from the original setup belongs to the actual geometric producers.
-/

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

theorem repairEntrance_actual_finite_plan_repair_endpoint
    (fixed : RepairEntranceProfiles)
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
    (Lprimary : ℕ)
    (hLocal : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Ref.cutoff nu))).card ≤ Lprimary)
    (hImmRef : IncrementsOriginalSliceImmersionInputs Ref)
    (lower : ℝ) (hEllRef : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Ref rho)
    (tolerance : ℝ) (hTolerance : 0 < tolerance)
    (C2 C442 : ℝ) (hC2 : 0 ≤ C2) (hC442 : 0 ≤ C442)
    (hMap2 : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
      smoothing.referenceMap) (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
      smoothing.closedSamples).toReal ≤ C2)
    (hMap442 : (paperAtlasCj 442 (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
      smoothing.referenceMap) (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
      smoothing.closedSamples).toReal ≤ C442)
    (envelope : ℕ → ℝ) (hEnvelope : ∀ j, smoothing.closedReferenceProfile j ≤ envelope j) :
    let theta := round3ParameterProductParent Ref.atlas smoothing.parameterFamily
      (squareNormalizedCutoff smoothing.sourcePreparation.raw)
      (tensorLocalNormalizedCutoff smoothing.parameterPreparation.raw)
    ∀ (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref smoothing.domain hsRef theta packet)
      (observer : RepairPrimaryObserverBudget Ref smoothing.domain hsRef theta packet profiles)
      (NumericMeta : ℕ → ℝ) (hNumericMeta : ∀ j, 0 ≤ NumericMeta j)
      (cutoff : RepairOriginalPrimaryCutoffJets Ref
        (round3ParameterWholePrimaryFamily Ref smoothing.domain hsRef hnRef theta
          (round3OuterReferencePrimaryPacket Ref smoothing.domain hsRef theta packet profiles)) NumericMeta)
      (hPrimaryParam : ∀ nu i a y, y ∈ tsupport (packet.piece nu i a).cutoff →
        y.1 ∈ Ref.parameterNormDomain i.2)
      (secondary : Round3PreparedParameterSecondaryPacket Ref smoothing.domain hsRef theta)
      (hPart : ∀ z, ∑ i, theta i z = 1)
      (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1))
      (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M))
      (hParam : ∀ r i a y, y ∈ (secondary.piece r i a).carrier → y.1 ∈ Ref.parameterNormDomain i.2)
      (numeric : IncrementSecondaryReferenceBudget Ref smoothing.domain hsRef theta secondary)
      (secondaryCharts : IncrementSecondaryChartBudget Ref smoothing.domain hsRef theta secondary),
    let phaseTolerance := min
      (repairEntranceGeometryTolerance m d N profiles.Tinv profiles.cF profiles.cT profiles.MH
        profiles.cF_pos profiles.cT_pos) (incrementSecondaryStabilityTolerance numeric)
    let geometryTolerance := min
      (repairEntranceGeometryTolerance m d N profiles.Tinv profiles.cF profiles.cT profiles.MH
        profiles.cF_pos profiles.cT_pos)
      (min (incrementSecondaryStabilityTolerance numeric) (incrementOriginalEllipticityTolerance (m+1) d N lower))
    let hPhaseTolerance : 0 < phaseTolerance := lt_min
      (repairEntranceGeometryTolerance_pos m d N profiles.Tinv profiles.Tinv_nonneg
        profiles.cF profiles.cT profiles.MH profiles.cF_pos profiles.cT_pos profiles.MH_nonneg)
      (incrementSecondaryStabilityTolerance_pos numeric)
    let hGeometryTolerance : 0 < geometryTolerance := lt_min
      (repairEntranceGeometryTolerance_pos m d N profiles.Tinv profiles.Tinv_nonneg
        profiles.cF profiles.cT profiles.MH profiles.cF_pos profiles.cT_pos profiles.MH_nonneg)
      (lt_min (incrementSecondaryStabilityTolerance_pos numeric)
        (incrementOriginalEllipticityTolerance_pos (m+1) d N lower hEllRef.lower_pos))
    let parameters := repairEntranceSelectedParameters m d N Ds Dp Lprimary radius hradius
      profiles.cF profiles.cT numeric.cT lower rho C2 (Given 0) phaseTolerance geometryTolerance tolerance
      hReserve.reserve_pos hC2 hPhaseTolerance hGeometryTolerance hTolerance
    let actual := repairEntranceSelectedProfiles BS0 TS0 BP0 TP0 observer.inverseProfile observer.forwardProfile
      Given reference envelope NumericMeta (secondaryCharts.cutoffProfile BS0 TS0 BP0 TP0 Ds Dp)
      secondaryCharts.inverseProfile secondaryCharts.forwardProfile hBS0 hTS0 hBP0 hTP0
      (fun j => ENNReal.toReal_nonneg.trans (smoothing.reference_bound j))
      (fun j => ENNReal.toReal_nonneg.trans (hEnvelope j))
    fixed.Prefix actual repairEntrancePrimitiveDepth →
    RepairEnvelopeConstructedRepair Ref smoothing envelope
      (parameters.entry.{uM,uP,0,0,0} (m := m) (d := d) (N := N) (M := M) fixed) parameters.epsilon parameters.eta C2 C442
        (Round3ParameterWholePrimaryIndex Ref theta packet)
        (Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hsRef theta secondary) Lprimary tolerance := by
  classical
  intro theta packet profiles observer NumericMeta hNumericMeta cutoff hPrimaryParam
    secondary hPart hCount hSupport hParam numeric secondaryCharts
    phaseTolerance geometryTolerance hPhaseTolerance hGeometryTolerance parameters actual hPrefix
  let base := repairEntranceLowFromMap (m+1) d N C2
  have hbase : 0 ≤ base := repairEntranceLowFromMap_nonneg _ _ _ hC2
  let budget := 4*(base+1)
  have hbudget : 0 < budget := by dsimp only [budget]; positivity
  let ML := max base (Given 0)
  have hML0 : 0 ≤ ML := hbase.trans (le_max_left _ _)
  have hRefProfile := round3_prepared_actual_reference_linear_profile Ref smoothing
    hReferenceMap hAll hNormSource hNormParameter
  have hUniformRefProfile : (incrementsOriginalInputProfileWithLinear Ref 0 1).toReal ≤ ML :=
    hRefProfile.2.trans (max_le_max
      (repairEntrance_reference_low_bound smoothing C2 hC2 hMap2) le_rfl)
  obtain ⟨hPart,hCount,hSupport,epsilonGeom,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
      hForwardExact,hInverseExact,hMetaExact,hTiExact,hCutExact,hObsExact,
      hEpsilonGeomExact,hEpsilonGeom,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,hByOrder⟩ :=
    increment_direct_numerical_literal_raw_before_metric Ref BS0 TS0 BP0 TP0
      hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius reference Given smoothing
      hReferenceMap hNormSource hNormParameter hAll hsRef hpRef hnRef hDecomp hLinear Lprimary hLocal hImmRef
      lower hEllRef rho hReserve budget ML hbudget.le hRefProfile.1 hUniformRefProfile
      packet profiles observer NumericMeta hNumericMeta cutoff hPrimaryParam
      secondary hPart hCount hSupport hParam numeric secondaryCharts
  subst ForwardC
  subst InverseC
  subst MetaC
  subst Tinv
  subst Kcut
  subst Tobs
  subst epsilonGeom
  let ForwardC := observer.forwardProfile
  let InverseC := observer.inverseProfile
  let MetaC := NumericMeta
  let Tinv := secondaryCharts.inverseProfile
  let Kcut := secondaryCharts.cutoffProfile BS0 TS0 BP0 TP0 Ds Dp
  let Tobs := secondaryCharts.forwardProfile
  let epsilonGeom := geometryTolerance
  let Β := Round3ParameterWholePrimaryIndex Ref theta packet
  let Sub := Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hsRef theta secondary
  obtain ⟨phaseEpsilon,hPhase,hPhaseExact,hEndpoint⟩ := repairEntrance_envelope_initialized_endpoint_from_map_bounds
    (Tr := ℝ) (Λ := Fin Ref.primaryCount) (Β := Β) (SubSecondary := Sub)
    smoothing hBS0 hTS0 hBP0 hTP0 hAll hReferenceMap.symm hNormSource hNormParameter
      hsRef hpRef hnRef hImmRef theta packet profiles hPrimaryParam secondary hParam
      numeric.nativeInverse numeric.nativeInverse_nonneg numeric.cF numeric.cT numeric.MH
      numeric.cF_pos numeric.cT_pos numeric.MH_nonneg numeric.first_value numeric.transverse_value
      numeric.hessian_bound numeric.inverse_bound ((Ds+1)*(Dp+1)) hPart hCount hSupport
      C2 C442 hC2 hC442 hMap2 hMap442 envelope hEnvelope
  have hPhaseToleranceExact : phaseEpsilon = phaseTolerance := hPhaseExact
  subst phaseEpsilon
  obtain ⟨CtargetReserved,hCtargetReserved,hCtargetNamed,hWithProfile⟩ := hEndpoint budget hbudget
  let Cnormal := fun r => round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
    InverseC ForwardC Given Ds Dp (40*(10+r+1)) budget profiles.cF profiles.cT
  let Cmap := fun r j => round4PreparedPairConstant (m+1) d radius hradius
    BS0 TS0 BP0 TP0 Ds Dp j (40*(10+r+1))
  let CtargetStage := Cmap
  choose hCnormal hCmap hCtargetStage Mrest Cut hMrestExact hMrest hCut
    CsGeom hCsGeomExact hCsGeom hSigmaGeom hPacket hRaw using (fun r => hByOrder (10+r) (Nat.le_add_right 10 r))
  let Packet := fun r => round4ParameterStageInputProfile m d N radius hradius BS0 TS0 BP0 TP0
    InverseC ForwardC Given reference Ds Dp (40*(10+r+1)) budget profiles.cF profiles.cT
  let localRefinementCount := (Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)
  let profile := fun r => round4ParameterCarrierCompletedProfile.{uM,uP,0,0}
    (m := m) (d := d) (N := N) (M := M)
    (fun j => CtargetReserved r j*budget+(j+1)*smoothing.closedReferenceProfile j)
    (40*(10+r+1)) localRefinementCount Lprimary localRefinementCount (by omega)
    (rho/4) (div_pos hReserve.reserve_pos (by norm_num)) (lower/4) (profiles.cT/16)
    (Packet r) ForwardC InverseC MetaC (hPacket r) (Mrest r) (Cut r) Tinv Tobs
  have hProfileIdentity : Round4ParameterSecondaryCompletedProfiles.{uM,uP,0,0}
      (m := m) (d := d) (N := N) (M := M)
      radius hradius Ds Dp BS0 TS0 BP0 TP0 Given reference smoothing.closedReferenceProfile
      budget Lprimary Unit profile CtargetReserved := by
    refine ⟨ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,profiles.cF,profiles.cT,
      rho/4,lower/4,profiles.cT/16,div_pos hReserve.reserve_pos (by norm_num),
      localRefinementCount,localRefinementCount,
      (fun _ : Unit => numeric.cT/16),hPacket,?_⟩
    intro r
    have hRestExact : Mrest r = round4ParameterSecondaryGeometryProfile m d N (40*(10+r+1))
        (fun _ : Unit => numeric.cT/16)
        (Packet r) Tinv Tobs (lower/4) := funext (hMrestExact r)
    have hCutExact : Cut r = fun j => Kcut (actualSecondarySolveOrder (40*(10+r+1)) j) :=
      funext (hCut r)
    dsimp only [profile]
    rw [hRestExact,hCutExact]
  let epsilon := min 1 (min phaseTolerance (min epsilonGeom tolerance))
  have hepsilon : 0 < epsilon := lt_min (by norm_num) (lt_min hPhase (lt_min hEpsilonGeom hTolerance))
  have hEpsOne : epsilon ≤ 1 := min_le_left _ _
  have hEpsPhase : epsilon ≤ phaseTolerance := (min_le_right _ _).trans (min_le_left _ _)
  have hEpsGeom : epsilon ≤ epsilonGeom :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hEpsTolerance : epsilon ≤ tolerance :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let L := ‖actualOriginalCoefficientFunctional (m+1)‖*ML
  have hL : 0 ≤ L := mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hML0
  let eta := rho/(4*(L+1))
  have heta : 0 < eta := div_pos hReserve.reserve_pos (by positivity)
  have hFixed : repairEntranceLowFromMap (m+1) d N C2+epsilon/4 ≤ budget/4 := by
    change base+epsilon/4 ≤ (4*(base+1))/4
    linarith
  let cap := fun r => round3RepairComputedGeometryThreshold (CsGeom r) budget (reference 0) L rho epsilonGeom
  have hCap : ∀ r, 0 < cap r := hSigmaGeom
  obtain ⟨cost,hNamedCosts,hWithCap⟩ := hWithProfile profile epsilon eta hepsilon heta hEpsPhase hFixed
  obtain ⟨Cs,sigma,hCsExact,hSigmaExact,hCs,hSigma,hSmall,hDisp,hTheta,hCapSmall,hWithEntry⟩ :=
    hWithCap cap hCap
  have hBudgetEnvelope (r : ℕ) :
      (fun j => CtargetReserved r j*budget+(j+1)*smoothing.closedReferenceProfile j) =
        parameters.targetBudget actual m d N (40*(10+r+1)) := by
    funext j
    rw [hCtargetNamed r j]
    exact repairEntranceCompensatedTargetCost_identity _ _ _ _ hbudget.ne' j
  have hProfilePlan : profile 0 = parameters.completedProfile.{uM,uP,0,0}
      (m := m) (d := d) (N := N) (M := M) actual 440 (by norm_num) := by
    have hRestExact : Mrest 0 = parameters.secondaryGeometry actual m d N 440 :=
      funext (hMrestExact 0)
    have hCutExact0 : Cut 0 = RepairEntranceParameters.cutoff actual 440 := funext (hCut 0)
    dsimp only [profile]
    rw [hBudgetEnvelope 0,hRestExact,hCutExact0]
    rfl
  have hPlanCost : Round4ParameterRepairCostIdentity.{uM,uP,0,0,0,0}
      (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
      (parameters.targetBudget actual m d N 440) 440 (by norm_num)
      (parameters.completedProfile.{uM,uP,0,0}
        (m := m) (d := d) (N := N) (M := M) actual 440 (by norm_num)) (cost 0) := by
    rw [← hProfilePlan,← hBudgetEnvelope 0]
    exact hNamedCosts 0
  let entry := parameters.entry.{uM,uP,0,0,0} (m := m) (d := d) (N := N) (M := M) fixed
  have hEntry : 0 < entry := parameters.entry_pos fixed
  have hEntryActual : entry ≤ sigma 0 := by
    have hh := repairEntrance_fixed_plan_entry_le_actual_block parameters fixed actual hPrefix Ref smoothing
      (cost 0) hPlanCost (hEnvelope 440) (hEnvelope 480)
    rw [hSigmaExact 0,hCsExact 0]
    have hCap0 : cap 0 = parameters.geometryCap actual m d 440 := by
      dsimp only [cap]
      rw [hCsGeomExact 0]
      rfl
    rw [hCap0]
    exact hh
  obtain ⟨t0,ht0,ht1,htEntry,hTExact,targetRadius,hRadius,hRadiusExact,hFinish⟩ :=
    hWithEntry entry hEntry hEntryActual
  refine ⟨budget,epsilon,eta,hbudget,hepsilon,heta,hEpsTolerance,
    rfl,rfl,rfl,profile,CtargetReserved,hCtargetNamed,(fun _ => rfl),hProfileIdentity,cost,Cs,sigma,hNamedCosts,hCsExact,cap,hCap,
    ⟨epsilonGeom,L,rho,hEpsilonGeom,hL,hReserve.reserve_pos,
      fun r => by dsimp only [cap]; rw [hCsGeomExact r]⟩,hSigmaExact,
    hCs,hSigma,hSmall,hDisp,hTheta,t0,ht0,ht1,htEntry,hTExact,targetRadius,hRadius,hRadiusExact,?_⟩
  intro metric hSym hSmooth hPositive hError changed
  obtain ⟨reserved,hTarget,hCost,hRun⟩ := hFinish metric hSym hSmooth hPositive
  apply hRun hError
  intro r v hv hv1 hvEntry state s hks hsk hNorm
  have hvCap : v ≤ cap r := hvEntry.trans (hCapSmall r).le
  have hvTheta : v < (reserved r).generated.cost.Theta^10 := by
    rw [hCost r]
    exact hvEntry.trans_lt (hTheta r)
  exact round4Parameter_literal_closed_raw_step_local Ref changed hsRef hAll hNormSource hNormParameter theta packet profiles secondary
    (10+r) Lprimary (Nat.le_add_right 10 r) budget ML lower rho hReserve.reserve_pos epsilonGeom (CsGeom r)
    (Packet r) ForwardC InverseC MetaC (Mrest r) (Cut r) Tinv Tobs (hPacket r)
    (hRaw r metric hSym hSmooth)
    (CtargetReserved r) (reserved r) (hTarget r) epsilon eta v hepsilon.le hEpsGeom le_rfl
    hv hv1 hvCap hvTheta state s hks


end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_actual_finite_plan_repair_endpoint
