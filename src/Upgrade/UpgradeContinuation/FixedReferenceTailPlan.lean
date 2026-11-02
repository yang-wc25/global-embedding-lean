import NormalPolar.ActualProbeProducedRepairPlan
import Probes.Round4ParameterNamedNormalRaw
import Probes.Round4ParameterClosedRawStep
import Probes.Round4ParameterReservedBeforeMetric
import Probes.Round3PreparedReferenceInputProfile

/-!
# A genuine restart and all probe tail caps from one fixed reference

The already proved reference factory manufactures its whole primary and
signed secondary packets, their chart profiles, and every future raw step.
This file retains those choices in the probe restart record.  The costs,
geometry entrance, and three original tail caps are chosen before any
starting scale or initial map.  A restart takes the supplied closed state
literally; its first map is never replaced by the reference initialization.

This uses the existing fixed-reference construction internally.  It makes
no claim about the separate finite-prefix requirement of the paper's
general repair proposition.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal BigOperators Classical

namespace GlobalEmbedding.Continuation.UpgradeContinuation

universe uM uP
variable {m d N : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [TopologicalSpace P] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IM) (n := ∞) P M

private local instance signedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

/-- The whole future probe repair run is produced from the fixed reference
geometry alone.  Neither a whole-primary/secondary packet, an observer
budget, a future raw solver, nor any final estimate is an input. -/
theorem probes_exists_fixed_reference_tail_plan
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (reference Given : ℕ → ℝ)
    (smoothing : Round3RepairFixedSmoothingPacket Ref BS TS BP TP Ds Dp
      radius hradius reference Given)
    (hReference : Ref.F = smoothing.referenceMap)
    (hSource : Ref.sourceNormDomain = smoothing.Omega)
    (hParameter : Ref.parameterNormDomain = smoothing.Q)
    (hAll : Ref.parameterSet = univ)
    (hs : IncrementsOriginalSmoothInputs Ref)
    (hp : IncrementsOriginalPhaseConditions Ref smoothing.domain hs)
    (hn : IncrementsOriginalFreeNormalConditions Ref smoothing.domain hs)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Ref)
    (hLinear : IncrementsOriginalLinearSmoothInputs Ref)
    (hImm : IncrementsOriginalSliceImmersionInputs Ref)
    (lower : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Ref rho)
    (tolerance : ℝ) (hTolerance : 0 < tolerance) :
    let theta := round3ParameterProductParent Ref.atlas smoothing.parameterFamily
      (squareNormalizedCutoff smoothing.sourcePreparation.raw)
      (tensorLocalNormalizedCutoff smoothing.parameterPreparation.raw)
    ∃ (primary : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (secondary : Round3PreparedParameterSecondaryPacket Ref smoothing.domain hs theta),
    ∃ plan : ActualProbeProducedRepairPlan smoothing
      (Round3ParameterWholePrimaryIndex Ref theta primary)
      (Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hs theta secondary),
      plan.epsilon ≤ tolerance := by
  intro theta
  let base := round3RepairReferenceLowBase smoothing
  have hbase : 0 ≤ base := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  let budget := 4*(base+1)
  have hbudget : 0 < budget := by dsimp only [budget]; positivity
  let ML := max base (Given 0)
  have hML : 0 ≤ ML := hbase.trans (le_max_left _ _)
  have hRefProfile := round3_prepared_actual_reference_linear_profile Ref smoothing
    hReference hAll hSource hParameter
  have hLocal : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Ref.cutoff nu))).card ≤
      Ref.primaryCount := by
    intro z
    exact (Finset.card_filter_le _ _).trans (by simp)
  obtain ⟨primary,profiles,secondary,hPart,hCount,hSupport,epsilonGeom,
      ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,hEpsilonGeom,hForwardC,hInverseC,hMetaC,
      hTinv,hKcut,hTobs,hByOrder⟩ :=
    round4Parameter_literal_raw_named_normal_before_metric Ref BS TS BP TP
      hBS hTS hBP hTP Ds Dp radius hradius reference Given smoothing
      hReference hSource hParameter hAll hs hp hn hDecomp hLinear Ref.primaryCount
      hLocal hImm lower hEll rho hReserve budget ML hbudget.le hRefProfile.1 hRefProfile.2
  let Β := Round3ParameterWholePrimaryIndex Ref theta primary
  let Sub := Round3ParameterOriginalSecondaryIndex Ref smoothing.domain hs theta secondary
  let Cnormal := fun k => round4SpatialReferenceNormalProfile m d N radius hradius BS TS BP TP
    InverseC ForwardC Given Ds Dp (40*(10+k+1)) budget profiles.cF profiles.cT
  let Cmap := fun k j => round4PreparedPairConstant (m+1) d radius hradius BS TS BP TP
    Ds Dp j (40*(10+k+1))
  choose hCnormal hCmap hCtarget Mrest Cut hMrestExact hMrest hCut
    CsGeom hCsGeomExact hCsGeom hSigmaGeom hPacket hRaw using
      (fun k => hByOrder (10+k) (Nat.le_add_right 10 k))
  let Packet := fun k j => max (Cmap k j*budget)
    (max (Cmap k j*budget+(j+1)*reference j) (max (Given j) (Cnormal k j)))
  let Ctarget := fun k j => round4SpatialPairConstant (m+1) d N radius hradius BS TS BP TP
    Ds Dp j (40*(10+k+1))
  let profile := fun k => round4LocalPrimaryLiteralRawProfile Ref smoothing hs theta primary profiles
    (40*(10+k+1)) Ref.primaryCount (by omega) budget lower (rho/4)
    (div_pos hReserve.reserve_pos (by norm_num)) (Packet k) ForwardC InverseC MetaC
    (hPacket k) (Ctarget k) (Mrest k) (Cut k) Tinv Tobs
  have hCostFactory (k : ℕ) :=
    round4Parameter_reserved_named_costs_before_metric
      (Tr := ℝ) (Λ := Fin Ref.primaryCount) (Β := Β) (SubSecondary := Sub)
      smoothing hBS hTS hBP hTP hAll (40*(10+k+1)) (by omega) budget
  choose cost hNamed hGetReserved using (fun k => (hCostFactory k).2 (profile k))
  let epsilon := min 1 (min epsilonGeom tolerance)
  have hepsilon : 0 < epsilon := lt_min (by norm_num) (lt_min hEpsilonGeom hTolerance)
  have hEpsOne : epsilon ≤ 1 := min_le_left _ _
  have hEpsGeom : epsilon ≤ epsilonGeom := (min_le_right _ _).trans (min_le_left _ _)
  let L := ‖actualOriginalCoefficientFunctional (m+1)‖*ML
  have hL : 0 ≤ L := mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hML
  let eta := rho/(4*(L+1))
  have heta : 0 < eta := div_pos hReserve.reserve_pos (by positivity)
  have hFixed : round3RepairReferenceLowBase smoothing+epsilon/4 ≤ budget/4 := by
    change base+epsilon/4 ≤ (4*(base+1))/4
    linarith
  let geometryCap := fun k =>
    round3RepairComputedGeometryThreshold (CsGeom k) budget (reference 0) L rho epsilonGeom
  let cap := fun k => min (geometryCap k) (round4ParameterProbeTailCap cost k)
  have hCap : ∀ k, 0 < cap k := fun k =>
    lt_min (hSigmaGeom k) (round4ParameterProbeTailCap_pos cost k)
  obtain ⟨Cs,sigma,hCsExact,hSigmaExact,hCs,hSigma,hSmall,hDisp,hTheta,hCapSmall,hRun⟩ :=
    round4Parameter_constructed_capped_infinite_blocks_before_metric
      (Tr := ℝ) (Λ := Fin Ref.primaryCount) (Β := Β) (SubSecondary := Sub)
      smoothing hBS hTS hBP hTP hAll cost budget epsilon eta
      hbudget hepsilon heta hFixed cap hCap
  choose reserved hTarget hCost using
    (fun k => hGetReserved k smoothing.metric smoothing.metric_symmetric smoothing.metric_smooth)
  refine ⟨primary,secondary,{
    budget := budget
    epsilon := epsilon
    eta := eta
    budget_pos := hbudget
    epsilon_pos := hepsilon
    eta_pos := heta
    reference_budget := by change 4*base < 4*(base+1); linarith
    cost := cost
    Cs := Cs
    sigma := sigma
    sigma_pos := hSigma
    small := hSmall
    displacement := hDisp
    threshold := hTheta
    tail_cap := fun k => (hCapSmall k).le.trans (min_le_right _ _)
    restart := ?_ },?_⟩
  · intro t ht ht1 htEntry initial
    apply hRun smoothing.metric smoothing.metric_symmetric smoothing.metric_smooth
      t ht ht1 htEntry initial
    intro k v hv hv1 hvEntry state s hks hsk hNorm
    have hvCap : v ≤ geometryCap k :=
      (hvEntry.trans (hCapSmall k).le).trans (min_le_left _ _)
    have hvTheta : v < (reserved k).generated.cost.Theta^10 := by
      rw [hCost k]
      exact hvEntry.trans_lt (hTheta k)
    obtain ⟨witness⟩ := round4Parameter_literal_closed_raw_step_local Ref smoothing hs
      hAll hSource hParameter theta primary profiles secondary
      (10+k) Ref.primaryCount (Nat.le_add_right 10 k) budget ML lower rho hReserve.reserve_pos
      epsilonGeom (CsGeom k) (Packet k) ForwardC InverseC MetaC (Mrest k) (Cut k) Tinv Tobs
      (hPacket k) (hRaw k smoothing.metric smoothing.metric_symmetric smoothing.metric_smooth)
      (Ctarget k) (reserved k) (hTarget k) epsilon eta v hepsilon.le hEpsGeom le_rfl
      hv hv1 hvCap hvTheta state s hks
    have actual := witness.toPrimitive smoothing
    rw [hCost k] at actual
    exact ⟨actual⟩
  · exact (min_le_right _ _).trans (min_le_right _ _)

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.probes_exists_fixed_reference_tail_plan
