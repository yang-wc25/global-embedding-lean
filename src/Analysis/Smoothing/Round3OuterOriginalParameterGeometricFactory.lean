import Smoothing.Round3OuterStablePrimaryProfiles
import Smoothing.Round3OuterStablePrimaryCrossData
import Smoothing.Round3OuterParameterFixedCarrierNormalStage
import Smoothing.ParameterRound2CompactNorms
import Smoothing.Round3OuterFixedCarrierProfileTransfer

/-! Original data produce one coherent actual normal and mean geometry.
The same stable primary family used in the normal proof is returned, and
its fixed-carrier observer profiles are selected at the reference map before
SF. The mean factory therefore consumes exactly these physical charts and
cutoffs, without an independent stage choice or a current-map maximum. -/

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

def Round3OuterParameterGeometricStageOutput
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
    (Cnormal ForwardC InverseC MetaC : ℕ → ℝ) (R : ℕ) : Prop :=
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
          (incrementsOriginalPhaseCovector Data nu z.1 z.2))

theorem round3_actual_original_parameter_geometric_factory
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref) (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hpRef : IncrementsOriginalPhaseConditions Ref hdRef hsRef)
    (hnRef : IncrementsOriginalFreeNormalConditions Ref hdRef hsRef)
    (hImmRef : IncrementsOriginalSliceImmersionInputs Ref)
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
    Round3OuterParameterGeometricStageOutput Ref hdRef hsRef hnRef theta packet profiles
      stage hF normal domain Cnormal ForwardC InverseC MetaC
      ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) := by
  intro theta
  obtain ⟨packet,profiles,hGeom0,epsilon,heps,hStable⟩ :=
    round3Parameter_actual_original_reference_factory Ref hdRef hsRef hpRef hnRef hImmRef hF0joint hAll
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp B hChart RS RP hOmega hQ hSource hParameter
  let g0 := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
    (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)
  let Rparent := (Ds+1)*(Dp+1)
  let R := Rparent*5^Module.finrank ℝ (Ep × D)
  have hScompact : ∀ i, IsCompact (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet i) := by
    rw [hAll]
    exact parameterRound2_originalEvaluation_univ_compact Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain hOmega hQ hdRef.source_norm_subset hdRef.parameter_norm_subset
  have hGCharts (nu) (a : Round3ParameterWholePrimaryIndex Ref theta packet) :=
    round3ParameterLiftedPrimaryChart_smooth Ref hdRef a.1.2 nu _
      (round3ParameterWholePrimaryPiece Ref hdRef theta (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles) nu a)
  obtain ⟨Forward,Inverse,Meta,hForward,hInverse,hMeta,hProfiles0⟩ :=
    round3_parameter_original_fixed_reference_profiles Ref hdRef g0 R hGeom0
      (fun nu a => (hGCharts nu a).1) (fun nu a => (hGCharts nu a).2) hScompact
  obtain ⟨hOpen0,hGeomC0,ForwardC,InverseC,MetaC,hForwardC,hInverseC,hMetaC,hProfilesC0⟩ :=
    round3_parameter_fixed_carrier_reference_profiles Ref hdRef g0 R hGeom0
      (fun nu a => (hGCharts nu a).1) (fun nu a => (hGCharts nu a).2) hScompact
  obtain ⟨C,hC,hMake⟩ := round3_exists_uniform_parameter_fixed_carrier_normal_stage
    (m := m) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 Inverse Forward Meta Given hBS0 hTS0 hBP0 hTP0 hInverse hForward hGiven
    Ds Dp radius hradius r budget (profiles.cF/16) (profiles.cT/16) (1/4)
    hbudget (div_pos profiles.cF_pos (by norm_num)) (div_pos profiles.cT_pos (by norm_num)) (by norm_num)
  refine ⟨packet,profiles,epsilon,C,ForwardC,InverseC,MetaC,heps,hC,hForwardC,hInverseC,hMetaC,?_⟩
  intro F H neighborhood Data reference givenPacket stage hd hs hDecomp S hF normal hFinite hBound
  have hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ F := by
    rw [← modelWithCornersSelf_prod]
    exact round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0
      Ds Dp radius hradius r budget reference givenPacket stage
  obtain ⟨stable⟩ := hStable (fun p x => F (p,x)) hFjoint hF hFinite hBound
  let ps := round3OuterStablePrimaryPacket Ref hdRef hsRef theta packet profiles (fun p x => F (p,x)) hF stable
  let g := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta ps
  have hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by rw [hChart]; exact hdRef.parameter_charts_smooth
  have hQT : ∀ i, Ref.parameterNormDomain i ⊆ (B.chart i).target := by rw [hChart]; exact hdRef.parameter_norm_subset
  obtain ⟨W,hW,hKW,hSmooth,hCompact,hSupport,hPart,hCount⟩ :=
    round3Parameter_actual_compact_product_parents BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp
      Ref.atlas B hdRef.atlas_smooth hB Ref.parameterSet RS RP Ref.sourceNormDomain Ref.parameterNormDomain
      hOmega hQ hdRef.source_norm_subset hQT hSource hParameter
  have hFullPart : ∀ z, ∑ i, theta i z = 1 := fun z => hPart z (hKW (by rw [hAll]; exact mem_univ _))
  have hg := round3_stable_primary_global_geometry_profiles Ref hdRef hsRef hnRef theta packet profiles
    Rparent hFullPart hCount Forward Inverse Meta (fun p x => F (p,x)) hF stable hProfiles0
  obtain ⟨e,hData,hNative,hActive,hInner,hChartActual,hFirst,hFrame,hReserve,hSlices⟩ :=
    round3_stable_primary_all_observer_data Ref hdRef hsRef hnRef theta packet profiles
      (fun p x => F (p,x)) hF stable
  let piece := round3ParameterWholePrimaryPiece Ref hdRef theta ps
  let host := fun nu (_ : Fin Ref.parameterCount) (a : Round3ParameterWholePrimaryIndex Ref theta packet) => (piece nu a).host
  let b := fun nu ip (a : Round3ParameterWholePrimaryIndex Ref theta packet) => round3ParameterCrossNativeChart
    (Ref.parameterChart a.1.2) (Ref.parameterChart ip) (piece nu a).native
  have hout := hMake Ref hdRef F H neighborhood reference givenPacket stage hd hs hAll hDecomp hReference
    (Round3ParameterWholePrimaryIndex Ref theta packet) g R hg.1 hg.2
    host b e hData hNative hActive hInner hChartActual hFirst hFrame hReserve hFixed hFixedBound
  have hSame := round3_stable_primary_global_functions Ref hdRef hsRef hnRef theta packet profiles
    (fun p x => F (p,x)) hF stable
  have hEta : g.eta = g0.eta := hSame.1
  obtain ⟨hOpen,hCover,hSub,hActive,hGeomC,rest⟩ :=
    round3_parameter_original_fixed_carrier Ref g R hg.1
  have hTransferred := round3_fixed_carrier_profiles_same_functions Ref hdRef g0 g R hg.1
    hSame.1 hSame.2.1 hSame.2.2.1 hOpen0 hOpen ForwardC InverseC MetaC hProfilesC0
  refine ⟨stable,hOpen,hg.1,hTransferred.2.1,?_⟩
  rw [hEta] at hout
  exact hout

#print axioms round3_actual_original_parameter_geometric_factory
end GlobalEmbedding.Continuation
