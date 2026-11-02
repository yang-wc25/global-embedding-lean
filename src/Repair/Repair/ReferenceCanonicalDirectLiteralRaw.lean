import Repair.IncrementDirectNumericalLiteralRaw
import Repair.ReferenceCanonicalLiteralStage
import Repair.IncrementDirectNumericalNamedNormal
import Probes.Round4ParameterLiteralPositiveStage
import Probes.Round4ParameterNamedNormalConsumers
import Smoothing.Round3ParameterLiteralCoherentBeforeMetric
import Smoothing.Round3OuterLiteralRawBeforeMetric
import Repair.ReferenceCanonicalLiteralStage

/-!
# Actual full repair increments with literal numerical geometry tolerance

The same primary, canonical mean, secondary solve and linear cross term
are constructed for each computed SF/SH stage. The selected reference
primary and secondary packets are fixed before the target metric. The
primary numerical stability tolerance and common secondary reserve enter
the actual literal raw witness factory without choosing either packet again.
No ideal step, raw solver witness, stage estimate or initial state is an
input to this theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators ENNReal
namespace GlobalEmbedding.Continuation
attribute [local irreducible] incrementCanonical_round3ParameterMeanNormCost incrementCanonical_round3ParameterMeanSizeCost
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

theorem referenceCanonical_direct_numerical_literal_raw_before_metric
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
    (budget ML : ℝ) (hbudget : 0 ≤ budget)
    (hProfile : incrementsOriginalInputProfileWithLinear Ref 0 1 ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear Ref 0 1).toReal ≤ ML) :
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
    let g0 := round3ParameterWholePrimaryFamily Ref smoothing.domain hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref smoothing.domain hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    (∀ z, ∑ i, theta i z = 1) ∧
    (∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)) ∧
    (∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M)) ∧
    ∃ (epsilon : ℝ) (ForwardC InverseC MetaC Tinv Kcut Tobs : ℕ → ℝ),
      ForwardC = observer.forwardProfile ∧ InverseC = observer.inverseProfile ∧
      MetaC = NumericMeta ∧
      Tinv = secondaryCharts.inverseProfile ∧
      Kcut = secondaryCharts.cutoffProfile BS0 TS0 BP0 TP0 Ds Dp ∧
      Tobs = secondaryCharts.forwardProfile ∧
      epsilon = min (repairEntranceGeometryTolerance m d N profiles.Tinv
        profiles.cF profiles.cT profiles.MH profiles.cF_pos profiles.cT_pos)
        (min (incrementSecondaryStabilityTolerance numeric)
          (incrementOriginalEllipticityTolerance (m+1) d N lower)) ∧
      0 < epsilon ∧ (∀ j, 0 ≤ ForwardC j) ∧
      (∀ j, 0 ≤ InverseC j) ∧ (∀ j, 0 ≤ MetaC j) ∧
      (∀ j, 0 ≤ Tinv j) ∧ (∀ j, 0 ≤ Kcut j) ∧ (∀ j, 0 ≤ Tobs j) ∧
    ∀ (k : ℕ) (hk : 10 ≤ k),
    let Cnormal := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
      InverseC ForwardC Given Ds Dp (40*(k+1)) budget profiles.cF profiles.cT
    (∀ j, 0 ≤ Cnormal j) ∧
    let Cmap := fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j (40*(k+1))
    let Ctarget := Cmap
    (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Ctarget j) ∧
    ∃ Mrest Cut : ℕ → ℝ,
      (∀ j, Mrest j = incrementUniformSecondaryGeometryProfile m d N (40*(k+1))
        (numeric.cT/16)
        (fun j => max (Cmap j*budget)
          (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j))))
        Tinv Tobs (lower/4) j) ∧
      (∀ j, 0 ≤ Mrest j) ∧
      (∀ j, Cut j = Kcut (actualSecondarySolveOrder (40*(k+1)) j)) ∧
    let Packet := fun j => max (Cmap j*budget)
      (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j)))
    ∃ Cs : ℝ, Cs = 2*round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp 0 (40*(k+1)) ∧
    0 ≤ Cs ∧
    let L := ‖actualOriginalCoefficientFunctional (m+1)‖*ML
    let sigma := round3RepairComputedGeometryThreshold Cs budget (reference 0) L rho epsilon
    0 < sigma ∧
    ∃ hPacket : ∀ j, 0 ≤ Packet j,
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Ref.atlas
        smoothing.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart i)),
    ReferenceCanonicalLocalPrimaryLiteralRawStageSupply Ref (smoothing.withMetric metric hSym hSmooth)
      hsRef theta packet profiles secondary
      k Lprimary hk budget ML lower rho hReserve.reserve_pos epsilon Cs
      Packet ForwardC InverseC MetaC Mrest Cut Tinv Tobs hPacket := by
  intro theta packet profiles observer NumericMeta hNumericMeta cutoff hPrimaryParam secondary hPart hCount hSupport hParam numeric secondaryCharts
  obtain ⟨hPart',hCount',hSupport',epsilon,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
      hForwardExact,hInverseExact,hMetaExact,hTiExact,hTcExact,hTfExact,hEpsilonExact,hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,hByOrder⟩ :=
    increment_direct_numerical_literal_coherent_before_metric Ref BS0 TS0 BP0 TP0
      hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius reference Given smoothing
      hReferenceMap hNormSource hNormParameter hAll hsRef hpRef hnRef hDecomp hLinear Lprimary hLocal hImmRef
      lower hEllRef rho hReserve budget ML hbudget hProfile hML
      packet profiles observer NumericMeta hNumericMeta cutoff hPrimaryParam secondary hPart hCount hSupport hParam numeric secondaryCharts
  refine ⟨hPart,hCount,hSupport,epsilon,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
    hForwardExact,hInverseExact,hMetaExact,hTiExact,hTcExact,hTfExact,hEpsilonExact,hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,?_⟩
  intro k hk
  let Cnormal := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
    InverseC ForwardC Given Ds Dp (40*(k+1)) budget profiles.cF profiles.cT
  let Cmap := fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j (40*(k+1))
  let Ctarget := Cmap
  obtain ⟨hCnormal,hCmap,hCtarget,Mrest,Cut,hMrestExact,hMrest,hCut,Cs,hCsExact,hCs,hSigma,hMake⟩ := hByOrder k hk
  let Packet := fun j => max (Cmap j*budget)
    (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j)))
  have hPacket : ∀ j, 0 ≤ Packet j := fun j =>
    (mul_nonneg (hCmap j) hbudget).trans (le_max_left _ _)
  refine ⟨hCnormal,hCmap,hCtarget,Mrest,Cut,hMrestExact,hMrest,hCut,Cs,hCsExact,hCs,hSigma,hPacket,?_⟩
  intro metric hSym hSmooth
  let changed := smoothing.withMetric metric hSym hSmooth
  intro CtargetReserved numerical reserved hTarget
    s hks t ht htSmall oldMap hOld hBudget S hMapFinite hMap hInherited ht1 state
    waveEpsilon delta hWave hWaveTheta
  obtain ⟨out,hOpen,hClose,actual⟩ := hMake metric hSym hSmooth s hks t ht htSmall oldMap hOld hBudget hMapFinite hMap hInherited
  let normal := fun nu => parameterRound2_intrinsicUnitFreeNormalField
    (fun p x => state.smoothedMap changed (p,x))
    (reserved.generated.data state).slice_smooth
    (fun p x => Ref.phase nu (p,x)) (Ref.freeNormal nu)
  obtain ⟨witness,hPrimary,hEta,hForward,hInverse⟩ :=
    referenceCanonical_round4_local_primary_coherent_conclusion_repair_increment Ref changed hsRef hnRef
      hAll hNormSource hNormParameter theta packet profiles secondary (by omega)
      ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) Lprimary ((Ds+1)*(Dp+1))
      lower (rho/4) (div_pos hReserve.reserve_pos (by norm_num))
      Cnormal _ ForwardC InverseC MetaC hPacket CtargetReserved Mrest Cut Tinv Tobs
      reserved hTarget state normal actual waveEpsilon delta hWave hWaveTheta
  exact ⟨witness⟩


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.referenceCanonical_direct_numerical_literal_raw_before_metric
