import Smoothing.Round4SpatialGeometryNamedMeta
import Smoothing.Round3OuterParameterAdmissibleBeforeOrder
import Probes.Round3PreparedOriginalParameterJointBeforeOrder
import Probes.Round3PreparedOriginalCoherentBeforeOrder
import Probes.Round4ParameterSecondaryStageConsumer

/-!
# The actual coherent increment preparation uses the named normal profile

The true phase, ellipticity, normal-rebound, primary and secondary
constructions are the existing physical constructions. Their normal
coefficient is now exactly the finite profile of the same returned
reference charts, through all three actual consumer boundaries. No
normal derivative estimate or prepared geometric output is assumed.
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

theorem round4Parameter_admissible_with_named_normal_before_order
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
    ∃ (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref hdRef hsRef theta packet),
    let g0 := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    ∃ (epsilon : ℝ) (ForwardC InverseC MetaC GeometryMeta : ℕ → ℝ),
      0 < epsilon ∧ (∀ j, 0 ≤ ForwardC j) ∧
      (∀ j, 0 ≤ InverseC j) ∧ (∀ j, 0 ≤ MetaC j) ∧
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
    Round3OuterParameterAdmissibleStageOutput Ref hdRef hsRef hnRef theta packet profiles
      stage hF normal domain Cnormal ForwardC InverseC GeometryMeta
      ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) lower := by
  intro theta
  obtain ⟨packet,jet,profiles,epsilon0,ForwardC,InverseC,GeometryMeta,hepsilon0,hForwardC,hInverseC,hGeometryMeta,hNamed,hPrimary⟩ :=
    round4_actual_spatial_parameter_geometric_named_meta_before_order Ref hdRef hsRef hpRef hnRef hImmRef hF0joint hAll
      hReference BS0 TS0 BP0 TP0 Given hBS0 hTS0 hBP0 hTP0 hGiven Ds Dp radius hradius
      B hChart RS RP hOmega hQ hSource hParameter hFixed hFixedBound
  let MetaC := round4WholeOriginalMetaProfile (m+1) d
    (fun v : Fin Ref.primaryCount × (Fin Ref.atlas.count × Fin Ref.parameterCount) => (jet v.1 v.2).mu)
    (fun v => (jet v.1 v.2).Mb) (fun v => (jet v.1 v.2).buffer)
    BS0 TS0 BP0 TP0 Given Ds Dp
  have hMetaC : ∀ j, 0 ≤ MetaC j := fun _ => round3PreparedFiniteMaximum_nonneg _
  obtain ⟨epsilonS,hepsilonS,hSigned⟩ := round3_prepared_actual_original_parameter_signed_good
    Ref hdRef hsRef hpRef hImmRef hAll hF0joint BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0
    Ds Dp B hChart RS RP hOmega hQ hSource hParameter
  obtain ⟨epsilonE,hepsilonE,hEll⟩ := round3_original_C2_coordinate_ellipticity Ref hdRef lower hEllRef hF0joint
  let epsilon := min epsilon0 (min epsilonS epsilonE)
  have hepsilon : 0 < epsilon := lt_min hepsilon0 (lt_min hepsilonS hepsilonE)
  refine ⟨packet,profiles,epsilon,ForwardC,InverseC,MetaC,GeometryMeta,hepsilon,hForwardC,hInverseC,hMetaC,hNamed,?_⟩
  intro r budget hbudget
  let Cnormal := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
    InverseC ForwardC Given Ds Dp r budget profiles.cF profiles.cT
  obtain ⟨hCnormal,hMake⟩ := hPrimary r budget hbudget
  refine ⟨hCnormal,?_⟩
  intro F H neighborhood Data reference givenPacket stage hd hs hDecomp S hF normal hFinite hBound
  obtain ⟨stable,hOpen,hGeom,hProfiles,rebound,hImm,hPrimary⟩ :=
    hMake F H neighborhood reference givenPacket stage hd hs hDecomp hFinite
      (hBound.trans (min_le_left _ _))
  have hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ F := by
    rw [← modelWithCornersSelf_prod]
    exact round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0
      Ds Dp radius hradius r budget reference givenPacket stage
  have hSignedF := hSigned (fun p x => F (p,x)) hFjoint hF hFinite
    (hBound.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hPhase := round3_prepared_parameter_rebound_phase_conditions Ref F hF H Ref.parameterOpen
    normal _ neighborhood hSignedF rebound.domain_conditions rebound.smooth_inputs hPrimary
  have hEllF := hEll F hFjoint hFinite
    (hBound.trans ((min_le_right _ _).trans (min_le_right _ _)))
  exact ⟨stable,hOpen,hGeom,hProfiles,rebound,hImm,hPrimary,hPhase,hEllF.lower_pos,hEllF.lower⟩


theorem round4Parameter_joint_with_named_normal_before_order
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
    ∃ (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref hdRef hsRef theta packet)
      (secondary : Round3PreparedParameterSecondaryPacket Ref hdRef hsRef theta),
    let g0 := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    (∀ z, ∑ i, theta i z = 1) ∧
    (∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)) ∧
    (∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M)) ∧
    ∃ (epsilon : ℝ) (ForwardC InverseC MetaC GeometryMeta Tinv Kcut Tobs : ℕ → ℝ),
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
  intro theta
  obtain ⟨packet,profiles,epsP,FC,IC,MC,GM,hepsP,hFC,hIC,hMC,hNamed,hPrimaryBefore⟩ :=
    round4Parameter_admissible_with_named_normal_before_order Ref hdRef hsRef hpRef hnRef hImmRef lower hEllRef
      hF0joint hAll hReference BS0 TS0 BP0 TP0 Given hBS0 hTS0 hBP0 hTP0 hGiven
      Ds Dp radius hradius B hChart RS RP hOmega hQ hSource hParameter hFixed hFixedBound
  obtain ⟨secondary,hPart,hCount,hSupport,Ti,Tc,Tf,epsS,hTi,hTc,hTf,hepsS,hSecondary⟩ :=
    round3_prepared_actual_original_parameter_raw_factory Ref hdRef hsRef hpRef hImmRef hAll hF0joint
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp B hChart RS RP hOmega hQ hSource hParameter
  refine ⟨packet,profiles,secondary,hPart,hCount,hSupport,min epsP epsS,FC,IC,MC,GM,Ti,Tc,Tf,
    lt_min hepsP hepsS,hFC,hIC,hMC,hTi,hTc,hTf,hNamed,?_⟩
  intro r budget hbudget
  let Cnormal := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
    IC FC Given Ds Dp r budget profiles.cF profiles.cT
  obtain ⟨hCn,hPrimary⟩ := hPrimaryBefore r budget hbudget
  refine ⟨hCn,?_⟩
  intro F H neighborhood Data reference givenPacket stage hd hs hDecomp S hF normal hFinite hBound
  have hPrimaryOut := hPrimary F H neighborhood reference givenPacket stage hd hs hDecomp hFinite
    (hBound.trans (min_le_left _ _))
  obtain ⟨stableP,hOpen,hGeom,hProfiles,rebound,hImm,hPrimaryGood,hPhase,hEll⟩ := hPrimaryOut
  have hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ F := by
    rw [← modelWithCornersSelf_prod]
    exact round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0
      Ds Dp radius hradius r budget reference givenPacket stage
  obtain ⟨stableS,hSigned,hRaw⟩ := hSecondary (fun p x => F (p,x)) hFjoint hF hFinite
    (hBound.trans (min_le_right _ _))
  refine ⟨rebound,?_,hImm,hPhase,hEll,stableS,?_⟩
  · exact ⟨stableP,hOpen,hGeom,hProfiles,rebound,hImm,hPrimaryGood,hPhase,hEll⟩
  · exact hRaw H Ref.parameterOpen normal _ neighborhood rebound.domain_conditions rebound.smooth_inputs hImm


theorem round4Parameter_coherent_with_named_normal_before_order
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
    ∃ (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref hdRef hsRef theta packet)
      (secondary : Round3PreparedParameterSecondaryPacket Ref hdRef hsRef theta),
    let g0 := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    (∀ z, ∑ i, theta i z = 1) ∧
    (∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)) ∧
    (∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M)) ∧
    ∃ (epsilon : ℝ) (ForwardC InverseC MetaC Tinv Kcut Tobs : ℕ → ℝ),
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
      (∀ j, Mrest j = round4ParameterSecondaryGeometryProfile m d N q
        (fun a : Round3ParameterOriginalSecondaryIndex Ref hdRef hsRef theta secondary =>
          (secondary.piece a.1 a.2.1 a.2.2).cT/16)
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
  intro theta
  obtain ⟨packet,profiles,secondary,hPart,hCount,hSupport,epsilon,ForwardC,InverseC,MetaC,GeometryMeta,Tinv,Kcut,Tobs,
      hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,hNamed,hByOrder⟩ :=
    round4Parameter_joint_with_named_normal_before_order Ref hdRef hsRef hpRef hnRef hImmRef lower hEllRef
      hF0joint hAll hReference BS0 TS0 BP0 TP0 Given hBS0 hTS0 hBP0 hTP0 hGiven
      Ds Dp radius hradius B hChart RS RP hOmega hQ hSource hParameter hFixed hFixedBound
  refine ⟨packet,profiles,secondary,hPart,hCount,hSupport,epsilon,ForwardC,InverseC,MetaC,Tinv,Kcut,Tobs,
    hepsilon,hForwardC,hInverseC,hMetaC,hTinv,hKcut,hTobs,?_⟩
  intro q budget hbudget
  let Cnormal := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
    InverseC ForwardC Given Ds Dp q budget profiles.cF profiles.cT
  obtain ⟨hCnormal,hMake⟩ := hByOrder q budget hbudget
  refine ⟨hCnormal,?_⟩
  intro reference
  let Cmap := fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j q
  let Ctarget := Cmap
  obtain ⟨hCmap,hCtarget,Mrest,Cut,hMrestExact,hMrest,hCut,hConsume⟩ :=
    round4Parameter_secondary_stage_raw_consumer Ref hdRef hsRef hnRef hAll hLinearRef theta packet profiles
      secondary hSupport hPart ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) Lprimary ((Ds+1)*(Dp+1)) hLocal hCount
      BS0 TS0 BP0 TP0 reference Given Cnormal ForwardC InverseC MetaC GeometryMeta Tinv Kcut Tobs
      hBS0 hTS0 hBP0 hTP0 hInverseC Ds Dp radius hradius q budget lower
  refine ⟨hCmap,hCtarget,Mrest,Cut,hMrestExact,hMrest,hCut,?_⟩
  intro Packet F H neighborhood Data stage hd hs hDecomp S hF normal hFinite hBound rho hReserve
  obtain ⟨rebound,hActual,hImm,hPhase,hEll,stable,hRaw⟩ :=
    hMake F H neighborhood reference Given stage hd hs hDecomp hFinite hBound
  exact hConsume F H neighborhood stage normal hNamed hActual rebound stable hRaw hDecomp rho hReserve


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4Parameter_admissible_with_named_normal_before_order
#print axioms GlobalEmbedding.Continuation.round4Parameter_joint_with_named_normal_before_order
#print axioms GlobalEmbedding.Continuation.round4Parameter_coherent_with_named_normal_before_order
