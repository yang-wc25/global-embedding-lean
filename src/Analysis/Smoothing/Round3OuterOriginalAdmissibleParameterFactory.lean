import Smoothing.Round3OuterOriginalParameterGeometricFactory
import Smoothing.Round3OuterOriginalEllipticityStability
import Probes.Round3PreparedParameterOriginalSignedGood
import Probes.Round3PreparedParameterStagePhaseConditions

/-! All original phase conditions and coordinate ellipticity accompany the
same whole-parameter stable geometry and actual new unit normal. One reference
C2 tolerance is chosen before the current SF, retaining the full signed and
doubled conditions on the physical support pair. -/

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

def Round3OuterParameterAdmissibleStageOutput
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref) (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hnRef : IncrementsOriginalFreeNormalConditions Ref hdRef hsRef)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hdRef hsRef theta packet)
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {r : ℕ} {budget : ℝ} {reference givenPacket : ℕ → ℝ}
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius r budget reference givenPacket)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (normal : Fin Data.primaryCount → P × M → Ey)
    (domain : Fin Data.primaryCount → Set (P × M))
    (Cnormal ForwardC InverseC MetaC : ℕ → ℝ) (R : ℕ) (lower : ℝ) : Prop :=
    ∃ stable : Round3ParameterWholeStableReference Ref hdRef hsRef theta packet profiles
        (fun p x => Data.F (p,x)) hF,
    let g := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
      (round3OuterStablePrimaryPacket Ref hdRef hsRef theta packet profiles
        (fun p x => Data.F (p,x)) hF stable)
    ∃ hOpen : ∀ nu, IsOpen (round3FixedCarrierDomain (g.eta nu)),
      Round3ParameterOriginalPrimaryGeometry Ref g R ∧
      Round3ParameterOriginalChartProfiles Ref
        (round3ParameterFixedCarrierFamily Ref g hOpen) ForwardC InverseC MetaC ∧
    ∃ rebound : Round3RepairNormalRebound stage normal domain Cnormal,
      let E := round3RepairRebindNormalData Data normal domain
      IncrementsOriginalSliceImmersionInputs E ∧
      (∀ nu z, z ∈ domain nu ∩ incrementsOriginalParameterRegion Data →
        GoodCovector (fun x => Data.F (z.1,x)) (hF z.1) z.2
          (incrementsOriginalPhaseCovector Data nu z.1 z.2)) ∧
      IncrementsOriginalPhaseConditions E rebound.domain_conditions rebound.smooth_inputs ∧
      IncrementsOriginalCoordinateEllipticityInputs E (lower/4)

theorem round3_actual_original_admissible_parameter_factory
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
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (r : ℕ)
    (budget : ℝ) (hbudget : 0 ≤ budget)
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
    ∃ (epsilon : ℝ) (Cnormal ForwardC InverseC MetaC : ℕ → ℝ),
      0 < epsilon ∧ (∀ j, 0 ≤ Cnormal j) ∧ (∀ j, 0 ≤ ForwardC j) ∧
      (∀ j, 0 ≤ InverseC j) ∧ (∀ j, 0 ≤ MetaC j) ∧
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
      stage hF normal domain Cnormal ForwardC InverseC MetaC
      ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) lower := by
  intro theta
  obtain ⟨packet,profiles,epsilon0,Cnormal,ForwardC,InverseC,MetaC,hepsilon0,hCnormal,hForwardC,hInverseC,hMetaC,hMake⟩ :=
    round3_actual_original_parameter_geometric_factory Ref hdRef hsRef hpRef hnRef hImmRef hF0joint hAll
      hReference BS0 TS0 BP0 TP0 Given hBS0 hTS0 hBP0 hTP0 hGiven Ds Dp radius hradius r budget hbudget
      B hChart RS RP hOmega hQ hSource hParameter hFixed hFixedBound
  obtain ⟨epsilonS,hepsilonS,hSigned⟩ := round3_prepared_actual_original_parameter_signed_good
    Ref hdRef hsRef hpRef hImmRef hAll hF0joint BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0
    Ds Dp B hChart RS RP hOmega hQ hSource hParameter
  obtain ⟨epsilonE,hepsilonE,hEll⟩ := round3_original_C2_coordinate_ellipticity Ref hdRef lower hEllRef hF0joint
  let epsilon := min epsilon0 (min epsilonS epsilonE)
  have hepsilon : 0 < epsilon := lt_min hepsilon0 (lt_min hepsilonS hepsilonE)
  refine ⟨packet,profiles,epsilon,Cnormal,ForwardC,InverseC,MetaC,hepsilon,hCnormal,hForwardC,hInverseC,hMetaC,?_⟩
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

#print axioms round3_actual_original_admissible_parameter_factory
end GlobalEmbedding.Continuation
