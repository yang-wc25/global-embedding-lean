import Repair.EntranceEndpointBeforeMetric
import Repair.IncrementUniformLiteralRaw
import Probes.Round4ParameterNamedNormalRaw
import Probes.Round3PreparedReferenceInputProfile
import Probes.Round4ParameterClosedRawStep
import Probes.Round4ParameterEndpointBeforeMetric
import Probes.Round4ParameterCompletedStagePrefix
import Probes.Round4ParameterSecondaryProfileIdentity
import Probes.Round4PrimaryLocalMultiplicity
import Smoothing.Round3OuterOriginalRepairEndpoint
import Probes.Round3ParameterActualCoherentConclusionRepair
import Smoothing.Round3RepairLiteralStage
import Smoothing.Round3OuterComputedStageOriginalInputs

/-!
# Actual repair using the selected numerical secondary reserve

The selected secondary packet is fixed before the target metric. The actual
raw factory reads its single numerical reserve, and the completed profile
records the resulting one-element numerical cost exactly, including when
the physical secondary index is empty. The construction reuses the actual
PR6 Round4 reference preparation,
canonical mean, raw solver and secondary correction.  It replaces the
input-dependent initialization by EntranceFromMapBounds.  In particular
there is no ideal step, supplied output estimate, or closed initial state
among the hypotheses.  The exact numerical budget, entrance scale and
C440 target radius are retained in the conclusion.

The remaining uniformity boundary is the original whole-reference geometry
and its named profiles.  This file does not infer that those profiles are
uniform merely from their existence for one particular reference packet.

The original fixed-reference assumptions produce the actual initial map,
all raw witnesses, the same least-wait trajectory and its exact smooth
phase-regular metric limit. This version additionally exposes the selected
literal spatial-smoothing target coefficient and all three numerical cost identities before
the target metric. The same raw witnesses consume the finite named normal
profile manufactured from the returned reference geometry. The canonical
mean and raw solver now consume the explicit ordinary-cutoff Meta profile
of the same chosen primary packet. The stronger full-carrier profile is
retained as an existential geometric certificate and does not enter the
numerical mean/repair costs. Its low chosen phase radii and reserves are
still geometric inputs to that named Meta formula. The actual reserved mean target consumes the genuine spatial-pair estimate via its proved one-way domination by the stronger working norm. It uses the existing stronger total-base2 internal
working norm; this does not prove same-order equivalence to the paper's
spatial-two-jet smoothing norm. Uniform generation of the primitive
reference profiles remains a separate source-equivalence obligation.
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

/-- A single target-independent set of numerical choices and one actual
natural-time trajectory for each allowed target. It records the literal
initial map and defect, every original norm convergence, exact induced
metric, joint smoothness, immersion and original phase conditions through
the actual phase-metric endpoint of that same trajectory. -/
def RepairUniformSecondaryConstructedRepair
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (C2 C442 : ℝ) (Β : Type uΒ) (SubSecondary : Type uSubSecondary) [Fintype Β] [Fintype SubSecondary] (Lprimary : ℕ) (rho : ℝ) : Prop :=
    ∃ budget epsilon eta : ℝ, 0 < budget ∧ 0 < epsilon ∧ 0 < eta ∧ epsilon ≤ rho ∧
    budget = 4*(repairEntranceLowFromMap (m+1) d N C2+1) ∧
    ∃ (profile : ℕ → Round3RepairPrimitiveProfiles) (Ctarget : ℕ → ℕ → ℝ),
    (∀ r j, Ctarget r j = round4SpatialPairConstant (m+1) d N radius hradius
      BS0 TS0 BP0 TP0 Ds Dp j (40*(10+r+1))) ∧
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
    t0 = repairEntranceScale budget epsilon (sigma 0)
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

/-- Forgetting the exposed numeric identities retains the exact previous
constructed-repair proposition, with the same trajectory and limit. -/
theorem RepairUniformSecondaryConstructedRepair.to_round3
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (C2 C442 : ℝ) (Β : Type uΒ) (SubSecondary : Type uSubSecondary) [Fintype Β] [Fintype SubSecondary]
    (Lprimary : ℕ) (rho : ℝ)
    (h : RepairUniformSecondaryConstructedRepair Ref smoothing C2 C442 Β SubSecondary Lprimary rho) :
    Round3OuterConstructedRepair Ref smoothing Β SubSecondary rho := by
  rcases h with ⟨budget,epsilon,eta,hb,he,het,hr,hBudgetExact,profile,Ctarget,hC,hL,hProfileIdentity,cost,Cs,sigma,
    hCosts,hCsExact,cap,hCap,hCapFormula,hSigmaExact,hCs,hSigma,hSmall,hDisp,hTheta,t0,ht0,ht1,htEntry,hTExact,targetRadius,hRadius,hRadiusExact,hFinish⟩
  exact ⟨budget,epsilon,eta,hb,he,het,hr,cost,Cs,sigma,hCs,hSigma,hSmall,hDisp,hTheta,
    t0,ht0,ht1,htEntry,targetRadius,hRadius,hFinish⟩

theorem repairEntrance_actual_uniform_secondary_constructed_repair_endpoint
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
      smoothing.closedSamples).toReal ≤ C442) :
    let theta := round3ParameterProductParent Ref.atlas smoothing.parameterFamily
      (squareNormalizedCutoff smoothing.sourcePreparation.raw)
      (tensorLocalNormalizedCutoff smoothing.parameterPreparation.raw)
    ∀ (secondary : Round3PreparedParameterSecondaryPacket Ref smoothing.domain hsRef theta)
      (hPart : ∀ z, ∑ i, theta i z = 1)
      (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1))
      (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M))
      (hParam : ∀ r i a y, y ∈ (secondary.piece r i a).carrier → y.1 ∈ Ref.parameterNormDomain i.2)
      (secondaryReserve : ℝ)
      (hSecondaryReserve : ∀ r i a, (secondary.piece r i a).cT = secondaryReserve),
    ∃ (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref smoothing.domain hsRef theta packet),
      RepairUniformSecondaryConstructedRepair Ref smoothing C2 C442
        (Round3ParameterWholePrimaryIndex Ref theta packet)
        (Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hsRef theta secondary) Lprimary tolerance := by
  classical
  intro theta secondary hPart hCount hSupport hParam secondaryReserve hSecondaryReserve
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
  obtain ⟨packet,profiles,hPart,hCount,hSupport,epsilonGeom,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
      hEpsilonGeom,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,hByOrder⟩ :=
    increment_uniform_literal_raw_before_metric Ref BS0 TS0 BP0 TP0
      hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius reference Given smoothing
      hReferenceMap hNormSource hNormParameter hAll hsRef hpRef hnRef hDecomp hLinear Lprimary hLocal hImmRef
      lower hEllRef rho hReserve budget ML hbudget.le hRefProfile.1 hUniformRefProfile
      secondary hPart hCount hSupport hParam secondaryReserve hSecondaryReserve
  let Β := Round3ParameterWholePrimaryIndex Ref theta packet
  let Sub := Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hsRef theta secondary
  obtain ⟨phaseEpsilon,hPhase,hEndpoint⟩ := repairEntrance_initialized_endpoint_from_map_bounds
    (Tr := ℝ) (Λ := Fin Ref.primaryCount) (Β := Β) (SubSecondary := Sub)
    smoothing hBS0 hTS0 hBP0 hTP0 hAll hReferenceMap.symm hNormSource hNormParameter
      hsRef hpRef hnRef hImmRef C2 C442 hC2 hC442 hMap2 hMap442
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
      (fun _ : Unit => secondaryReserve/16),hPacket,?_⟩
    intro r
    have hRestExact : Mrest r = round4ParameterSecondaryGeometryProfile m d N (40*(10+r+1))
        (fun _ : Unit => secondaryReserve/16)
        (Packet r) Tinv Tobs (lower/4) := funext (hMrestExact r)
    have hCutExact : Cut r = fun j => Kcut (actualSecondarySolveOrder (40*(10+r+1)) j) :=
      funext (hCut r)
    dsimp only [profile]
    rw [hRestExact,hCutExact]
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
  have hFixed : repairEntranceLowFromMap (m+1) d N C2+epsilon/4 ≤ budget/4 := by
    change base+epsilon/4 ≤ (4*(base+1))/4
    linarith
  let cap := fun r => round3RepairComputedGeometryThreshold (CsGeom r) budget (reference 0) L rho epsilonGeom
  have hCap : ∀ r, 0 < cap r := hSigmaGeom
  obtain ⟨cost,hNamedCosts,hWithCap⟩ := hWithProfile profile epsilon eta hepsilon heta hEpsPhase hFixed
  obtain ⟨Cs,sigma,hCsExact,hSigmaExact,hCs,hSigma,hSmall,hDisp,hTheta,hCapSmall,t0,ht0,ht1,htEntry,hTExact,targetRadius,hRadius,hRadiusExact,hFinish⟩ :=
    hWithCap cap hCap
  refine ⟨packet,profiles,budget,epsilon,eta,hbudget,hepsilon,heta,hEpsTolerance,
    rfl,profile,CtargetReserved,hCtargetNamed,(fun _ => rfl),hProfileIdentity,cost,Cs,sigma,hNamedCosts,hCsExact,cap,hCap,
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


#print axioms repairEntrance_actual_uniform_secondary_constructed_repair_endpoint
#print axioms RepairUniformSecondaryConstructedRepair.to_round3
end GlobalEmbedding.Continuation
