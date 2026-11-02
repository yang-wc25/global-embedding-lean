import Repair.EntranceDirectMetaGeometry
import Repair.EntranceUniformStableFamily
import Repair.IncrementExactNumericalSecondaryFactory
import Repair.IncrementNumericalEllipticity
import Repair.IncrementUniformStageConsumer
import Probes.Round4ParameterNamedNormalConsumers
import Smoothing.Round4SpatialGeometryNamedMeta
import Smoothing.Round3OuterParameterAdmissibleBeforeOrder
import Probes.Round3PreparedOriginalParameterJointBeforeOrder
import Probes.Round3PreparedOriginalCoherentBeforeOrder
import Probes.Round4ParameterSecondaryStageConsumer

/-!
# The actual joint stage with one numerical geometry tolerance

The actual selected primary profiles enter the numerical whole-reference
stability theorem. The actual selected secondary packet supplies its own
stable signed-phase proof. Neither reference packet is chosen again.
The complete actual coherent stage then consumes the common numerical
secondary cost while preserving the original solver witnesses and norms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
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

private local instance namedNormalSignedFinite (n : ℕ) :
    Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem increment_direct_numerical_joint_named_normal_before_order
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref) (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hpRef : IncrementsOriginalPhaseConditions Ref hdRef hsRef)
    (hnRef : IncrementsOriginalFreeNormalConditions Ref hdRef hsRef)
    (hImmRef : IncrementsOriginalSliceImmersionInputs Ref)
    (lower : ℝ) (hEllRef : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F)
    (hAll : Ref.parameterSet = univ)
    (hReference : ∀ p ∈ Ref.parameterOpen, ∀ x, Ref.reference p x ≠ 0)
    (BS0 TS0 BP0 TP0 Given : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (hGiven : ∀ j, 0 ≤ Given j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (B : TensorBufferedChartFamily (Fin Ref.parameterCount) P Ep)
    (hChart : B.chart = Ref.parameterChart)
    (RS : TensorRawCutoffPreparation Ref.atlas BS0 TS0 Ds)
    (RP : TensorLocalRawPreparation B Ref.parameterSet BP0 TP0 Dp)
    (hOmega : ∀ i, IsCompact (Ref.sourceNormDomain i))
    (hQ : ∀ i, IsCompact (Ref.parameterNormDomain i))
    (hSource : ∀ i, bufferedSamplingCoordinates Ref.atlas i ⊆ Ref.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Ref.parameterNormDomain i)
    (hFixed : ∀ j, parameterRound2_originalFixedPacketProfile Ref j 1 ≠ ⊤)
    (hFixedBound : ∀ j, (parameterRound2_originalFixedPacketProfile Ref j 1).toReal ≤ Given j) :
    let theta := round3ParameterProductParent Ref.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∀ (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref hdRef hsRef theta packet)
      (observer : RepairPrimaryObserverBudget Ref hdRef hsRef theta packet profiles)
      (NumericMeta : ℕ → ℝ) (hNumericMeta : ∀ j, 0 ≤ NumericMeta j)
      (cutoff : RepairOriginalPrimaryCutoffJets Ref
        (round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
          (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)) NumericMeta)
      (hPrimaryParam : ∀ nu i a y, y ∈ tsupport (packet.piece nu i a).cutoff →
        y.1 ∈ Ref.parameterNormDomain i.2)
      (secondary : Round3PreparedParameterSecondaryPacket Ref hdRef hsRef theta)
      (hPart : ∀ z, ∑ i, theta i z = 1)
      (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1))
      (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M))
      (hParam : ∀ r i a y, y ∈ (secondary.piece r i a).carrier → y.1 ∈ Ref.parameterNormDomain i.2)
      (numeric : IncrementSecondaryReferenceBudget Ref hdRef hsRef theta secondary)
      (secondaryCharts : IncrementSecondaryChartBudget Ref hdRef hsRef theta secondary),
    let g0 := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    (∀ z, ∑ i, theta i z = 1) ∧
    (∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)) ∧
    (∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M)) ∧
    ∃ (epsilon : ℝ) (ForwardC InverseC MetaC GeometryMeta Tinv Kcut Tobs : ℕ → ℝ),
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
      Round3ParameterOriginalChartProfiles Ref g0 ForwardC InverseC MetaC ∧
    ∀ (r : ℕ) (budget : ℝ), 0 ≤ budget →
    let Cnormal := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
      InverseC ForwardC Given Ds Dp r budget profiles.cF profiles.cT
    (∀ j, 0 ≤ Cnormal j) ∧
    ∀ (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
    let Data := round3ParameterStageData Ref F H Ref.parameterOpen Ref.freeNormal Ref.primaryDomain neighborhood
    ∀ (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius r budget reference givenPacket)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data),
    let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference givenPacket stage) p
    let normal := fun nu => parameterRound2_intrinsicUnitFreeNormalField
      (fun p x => Data.F (p,x)) hF (fun p x => Data.phase nu (p,x)) (Data.freeNormal nu)
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart (fun z => F z-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart (fun z => F z-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ epsilon →
    ∃ rebound : Round3RepairNormalRebound stage normal domain Cnormal,
      let E := round3RepairRebindNormalData Data normal domain
      Round3OuterParameterAdmissibleStageOutput Ref hdRef hsRef hnRef theta packet profiles
        stage hF normal domain Cnormal ForwardC InverseC GeometryMeta
        ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) lower ∧
      IncrementsOriginalSliceImmersionInputs E ∧
      IncrementsOriginalPhaseConditions E rebound.domain_conditions rebound.smooth_inputs ∧
      IncrementsOriginalCoordinateEllipticityInputs E (lower/4) ∧
      ∃ stable : ∀ r i (a : secondary.s r i),
        Round3PreparedParameterStableSecondaryPiece Ref hdRef hsRef i r _ (secondary.piece r i a)
          (fun p x => Data.F (p,x)) hF,
      ∀ r i (a : secondary.s r i) observer,
      let choice := round3PreparedParameterSecondaryChoice Ref hdRef hsRef i r _ (stable r i a).piece
      ∃ out : Round3PreparedParameterRawPiece E rebound.domain_conditions rebound.smooth_inputs (i.1,observer) r
        ((Ref.parameterChart observer).target ×ˢ (univ : Set M))
        (fun v : Fin Ref.atlas.count => Ref.atlas.chart v)
        (fun v => (parameterTensorModelEquiv (m+1) d) ⁻¹'
          incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet (v,observer)),
        out.choice = (choice.pullback (Ref.parameterChart observer)).toNative ∧
        out.Tinv = Tinv ∧ out.Kcut = Kcut ∧ out.Tobs = Tobs ∧
        out.cT = (secondary.piece r i a).cT/16 ∧ out.Bnative = 1+Tobs 1 := by
  intro theta packet profiles observer NumericMeta hNumericMeta cutoff hPrimaryParam secondary hPart hCount hSupport hParam numeric secondaryCharts
  let epsP := repairEntranceGeometryTolerance m d N profiles.Tinv
    profiles.cF profiles.cT profiles.MH profiles.cF_pos profiles.cT_pos
  have hepsP : 0 < epsP := repairEntranceGeometryTolerance_pos m d N profiles.Tinv
    profiles.Tinv_nonneg profiles.cF profiles.cT profiles.MH profiles.cF_pos profiles.cT_pos profiles.MH_nonneg
  have hStable := repairEntrance_uniform_whole_reference_stable_family Ref hdRef hsRef hnRef
    hF0joint hAll theta packet profiles hPrimaryParam
  obtain ⟨FC,IC,GM,hFCExact,hICExact,hepsP',hFC,hIC,hGM,hNamed,hPrimaryBefore⟩ :=
    repairEntrance_direct_meta_geometric_before_order Ref hdRef hsRef hpRef hnRef hImmRef
      hF0joint hAll hReference BS0 TS0 BP0 TP0 Given hBS0 hTS0 hBP0 hTP0 hGiven
      Ds Dp radius hradius B hChart RS RP hOmega hQ hSource hParameter hFixed hFixedBound
      packet profiles observer NumericMeta hNumericMeta cutoff epsP hepsP hStable
  let MC := NumericMeta
  have hMC : ∀ j, 0 ≤ MC j := hNumericMeta
  obtain ⟨Ti,Tc,Tf,epsS,hTiExact,hTcExact,hTfExact,hEpsSExact,hTi,hTc,hTf,hepsS,hSecondary⟩ :=
    increment_exact_numerical_secondary_raw_factory Ref hdRef hsRef hAll hF0joint
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp B hChart RS RP
      secondary hPart hSupport hParam numeric secondaryCharts
  let epsE := incrementOriginalEllipticityTolerance (m+1) d N lower
  have hepsE := incrementOriginalEllipticityTolerance_pos (m+1) d N lower hEllRef.lower_pos
  have hEll := increment_original_C2_coordinate_ellipticity Ref hdRef lower hEllRef hF0joint
  have hEpsExact : min epsP (min epsS epsE) =
      min (repairEntranceGeometryTolerance m d N profiles.Tinv
        profiles.cF profiles.cT profiles.MH profiles.cF_pos profiles.cT_pos)
        (min (incrementSecondaryStabilityTolerance numeric)
          (incrementOriginalEllipticityTolerance (m+1) d N lower)) := by
    rw [hEpsSExact]
  refine ⟨hPart,hCount,hSupport,min epsP (min epsS epsE),FC,IC,MC,GM,Ti,Tc,Tf,
    hFCExact,hICExact,rfl,hTiExact,hTcExact,hTfExact,hEpsExact,lt_min hepsP (lt_min hepsS hepsE),hFC,hIC,hMC,hTi,hTc,hTf,hNamed,?_⟩
  intro r budget hbudget
  let Cnormal := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
    IC FC Given Ds Dp r budget profiles.cF profiles.cT
  obtain ⟨hCn,hPrimary⟩ := hPrimaryBefore r budget hbudget
  refine ⟨hCn,?_⟩
  intro F H neighborhood Data reference givenPacket stage hd hs hDecomp S hF normal hFinite hBound
  obtain ⟨stableP,hOpen,hGeom,hProfiles,rebound,hImm,hPrimaryGood⟩ :=
    hPrimary F H neighborhood reference givenPacket stage hd hs hDecomp hFinite
      (hBound.trans (min_le_left _ _))
  have hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ F := by
    rw [← modelWithCornersSelf_prod]
    exact round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0
      Ds Dp radius hradius r budget reference givenPacket stage
  obtain ⟨stableS,hSigned,hRaw⟩ := hSecondary (fun p x => F (p,x)) hFjoint hF hFinite
    (hBound.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hPhase := round3_prepared_parameter_rebound_phase_conditions Ref F hF H Ref.parameterOpen
    normal _ neighborhood hSigned rebound.domain_conditions rebound.smooth_inputs hPrimaryGood
  have hEllF := hEll F hFjoint hFinite
    (hBound.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨rebound,?_,hImm,hPhase,?_,stableS,?_⟩
  · exact ⟨stableP,hOpen,hGeom,hProfiles,rebound,hImm,hPrimaryGood,hPhase,hEllF.lower_pos,hEllF.lower⟩
  · exact ⟨hEllF.lower_pos,hEllF.lower⟩
  · exact hRaw H Ref.parameterOpen normal _ neighborhood rebound.domain_conditions rebound.smooth_inputs hImm


theorem increment_direct_numerical_coherent_named_normal_before_order
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref) (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hpRef : IncrementsOriginalPhaseConditions Ref hdRef hsRef)
    (hnRef : IncrementsOriginalFreeNormalConditions Ref hdRef hsRef)
    (hImmRef : IncrementsOriginalSliceImmersionInputs Ref)
    (lower : ℝ) (hEllRef : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F)
    (hAll : Ref.parameterSet = univ)
    (hReference : ∀ p ∈ Ref.parameterOpen, ∀ x, Ref.reference p x ≠ 0)
    (hLinearRef : IncrementsOriginalLinearSmoothInputs Ref)
    (Lprimary : ℕ)
    (hLocal : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Ref.cutoff nu))).card ≤ Lprimary)
    (BS0 TS0 BP0 TP0 Given : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (hGiven : ∀ j, 0 ≤ Given j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (B : TensorBufferedChartFamily (Fin Ref.parameterCount) P Ep)
    (hChart : B.chart = Ref.parameterChart)
    (RS : TensorRawCutoffPreparation Ref.atlas BS0 TS0 Ds)
    (RP : TensorLocalRawPreparation B Ref.parameterSet BP0 TP0 Dp)
    (hOmega : ∀ i, IsCompact (Ref.sourceNormDomain i))
    (hQ : ∀ i, IsCompact (Ref.parameterNormDomain i))
    (hSource : ∀ i, bufferedSamplingCoordinates Ref.atlas i ⊆ Ref.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Ref.parameterNormDomain i)
    (hFixed : ∀ j, parameterRound2_originalFixedPacketProfile Ref j 1 ≠ ⊤)
    (hFixedBound : ∀ j, (parameterRound2_originalFixedPacketProfile Ref j 1).toReal ≤ Given j) :
    let theta := round3ParameterProductParent Ref.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∀ (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref hdRef hsRef theta packet)
      (observer : RepairPrimaryObserverBudget Ref hdRef hsRef theta packet profiles)
      (NumericMeta : ℕ → ℝ) (hNumericMeta : ∀ j, 0 ≤ NumericMeta j)
      (cutoff : RepairOriginalPrimaryCutoffJets Ref
        (round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
          (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)) NumericMeta)
      (hPrimaryParam : ∀ nu i a y, y ∈ tsupport (packet.piece nu i a).cutoff →
        y.1 ∈ Ref.parameterNormDomain i.2)
      (secondary : Round3PreparedParameterSecondaryPacket Ref hdRef hsRef theta)
      (hPart : ∀ z, ∑ i, theta i z = 1)
      (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1))
      (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M))
      (hParam : ∀ r i a y, y ∈ (secondary.piece r i a).carrier → y.1 ∈ Ref.parameterNormDomain i.2)
      (numeric : IncrementSecondaryReferenceBudget Ref hdRef hsRef theta secondary)
      (secondaryCharts : IncrementSecondaryChartBudget Ref hdRef hsRef theta secondary),
    let g0 := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)
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
    ∀ (q : ℕ) (budget : ℝ), 0 ≤ budget →
    let Cnormal := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
      InverseC ForwardC Given Ds Dp q budget profiles.cF profiles.cT
    (∀ j, 0 ≤ Cnormal j) ∧
    ∀ reference : ℕ → ℝ,
    let Cmap := fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j q
    let Ctarget := Cmap
    (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Ctarget j) ∧
    ∃ Mrest Cut : ℕ → ℝ,
      (∀ j, Mrest j = incrementUniformSecondaryGeometryProfile m d N q
        (numeric.cT/16)
        (fun j => max (Cmap j*budget)
          (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j))))
        Tinv Tobs (lower/4) j) ∧
      (∀ j, 0 ≤ Mrest j) ∧
      (∀ j, Cut j = Kcut (actualSecondarySolveOrder q j)) ∧
    let Packet := fun j => max (Cmap j*budget)
      (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j)))
    ∀ (F : P × M → Ey)
      (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
    let Data := round3ParameterStageData Ref F H Ref.parameterOpen Ref.freeNormal Ref.primaryDomain neighborhood
    ∀ (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius q budget reference Given)
      (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
      (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data),
    let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius q budget reference Given stage) p
    let normal := fun nu => parameterRound2_intrinsicUnitFreeNormalField
      (fun p x => Data.F (p,x)) hF (fun p x => Data.phase nu (p,x)) (Data.freeNormal nu)
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart (fun z => F z-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart (fun z => F z-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ epsilon →
    ∀ rho : ℝ, IncrementsOriginalDecompositionReserveInputs Data rho →
    Round4LocalPrimaryCoherentConclusion Ref hdRef hsRef hnRef theta packet profiles secondary F H neighborhood
      stage hF normal Cnormal ForwardC InverseC MetaC Packet Mrest Cut Tinv Tobs
      ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) Lprimary ((Ds+1)*(Dp+1)) lower rho := by
  intro theta packet profiles observer NumericMeta hNumericMeta cutoff hPrimaryParam secondary hPart hCount hSupport hParam numeric secondaryCharts
  obtain ⟨hPart',hCount',hSupport',epsilon,ForwardC,InverseC,MetaC,GeometryMeta,Tinv,Kcut,Tobs,
      hForwardExact,hInverseExact,hMetaExact,hTiExact,hTcExact,hTfExact,hEpsilonExact,hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,hNamed,hByOrder⟩ :=
    increment_direct_numerical_joint_named_normal_before_order Ref hdRef hsRef hpRef hnRef hImmRef lower hEllRef
      hF0joint hAll hReference BS0 TS0 BP0 TP0 Given hBS0 hTS0 hBP0 hTP0 hGiven
      Ds Dp radius hradius B hChart RS RP hOmega hQ hSource hParameter hFixed hFixedBound
      packet profiles observer NumericMeta hNumericMeta cutoff hPrimaryParam secondary hPart hCount hSupport hParam numeric secondaryCharts
  refine ⟨hPart,hCount,hSupport,epsilon,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
    hForwardExact,hInverseExact,hMetaExact,hTiExact,hTcExact,hTfExact,hEpsilonExact,hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,?_⟩
  intro q budget hbudget
  let Cnormal := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
    InverseC ForwardC Given Ds Dp q budget profiles.cF profiles.cT
  obtain ⟨hCnormal,hMake⟩ := hByOrder q budget hbudget
  refine ⟨hCnormal,?_⟩
  intro reference
  let Cmap := fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j q
  let Ctarget := Cmap
  obtain ⟨hCmap,hCtarget,Mrest,Cut,hMrestExact,hMrest,hCut,hConsume⟩ :=
    increment_uniform_secondary_stage_raw_consumer Ref hdRef hsRef hnRef hAll hLinearRef theta packet profiles
      secondary numeric.cT numeric.transverse_value hSupport hPart ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) Lprimary ((Ds+1)*(Dp+1)) hLocal hCount
      BS0 TS0 BP0 TP0 reference Given Cnormal ForwardC InverseC MetaC GeometryMeta Tinv Kcut Tobs
      hBS0 hTS0 hBP0 hTP0 hInverseC Ds Dp radius hradius q budget lower
  refine ⟨hCmap,hCtarget,Mrest,Cut,hMrestExact,hMrest,hCut,?_⟩
  intro Packet F H neighborhood Data stage hd hs hDecomp S hF normal hFinite hBound rho hReserve
  obtain ⟨rebound,hActual,hImm,hPhase,hEll,stable,hRaw⟩ :=
    hMake F H neighborhood reference Given stage hd hs hDecomp hFinite hBound
  exact hConsume F H neighborhood stage normal hNamed hActual rebound stable hRaw hDecomp rho hReserve


end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.increment_direct_numerical_joint_named_normal_before_order
#print axioms GlobalEmbedding.Continuation.increment_direct_numerical_coherent_named_normal_before_order
