import Smoothing.Round4SpatialParameterGeometryBeforeOrder
import Smoothing.Round4ReferenceFactoryProfiles
import Smoothing.Round4WholeOriginalMeta
import Smoothing.Round3OuterOriginalParameterGeometricFactory
import Smoothing.Round4SpatialParameterFixedCarrierNormalStage
import Smoothing.Round4SpatialReferenceNormalProfile

/-! One reference tolerance and one physical primary packet work for ALL
smoothing orders and budgets. The numerical normal cost is the named finite function of the SAME
returned reference profiles, evaluated at r and budget. This order of quantifiers supplies the common C2 neighborhood
required by the actual infinite repair schedule; no infimum of stagewise
positive tolerances is used. -/

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

theorem round4_actual_spatial_parameter_geometric_named_meta_before_order
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
      (jet : ∀ nu i, Round4PrimaryJetSupply Ref i nu
        ((Ref.parameterChart i.2).target ×ˢ (univ : Set M))
        (round3ParameterNativeParent (Ref.parameterChart i.2) (theta i))
        (packet.s nu i) (packet.piece nu i))
      (profiles : Round3ParameterWholeReferenceProfiles Ref hdRef hsRef theta packet),
    let g0 := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    let NumericMeta := round4WholeOriginalMetaProfile (m+1) d
      (fun v : Fin Ref.primaryCount × (Fin Ref.atlas.count × Fin Ref.parameterCount) => (jet v.1 v.2).mu)
      (fun v => (jet v.1 v.2).Mb) (fun v => (jet v.1 v.2).buffer) BS0 TS0 BP0 TP0 Given Ds Dp
    ∃ (epsilon : ℝ) (ForwardC InverseC MetaC : ℕ → ℝ),
      0 < epsilon ∧ (∀ j, 0 ≤ ForwardC j) ∧
      (∀ j, 0 ≤ InverseC j) ∧ (∀ j, 0 ≤ MetaC j) ∧
      Round3ParameterOriginalChartProfiles Ref g0 ForwardC InverseC NumericMeta ∧
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
    Round3OuterParameterGeometricStageOutput Ref hdRef hsRef hnRef theta packet profiles
      stage hF normal domain Cnormal ForwardC InverseC MetaC
      ((Ds+1)*(Dp+1)*5^Module.finrank ℝ (Ep × D)) := by
  intro theta
  obtain ⟨packet,hPacketJets,profiles,hGeom0,epsilon,heps,hStable⟩ :=
    round4Parameter_actual_original_reference_factory_profiles Ref hdRef hsRef hpRef hnRef hImmRef hF0joint hAll
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp B hChart RS RP hOmega hQ hSource hParameter
  let jet := fun nu i => Classical.choice (hPacketJets nu i)
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
  obtain ⟨Forward0,Inverse0,Meta0,hForward0,hInverse0,hMeta0,hProfiles00⟩ :=
    round3_parameter_original_fixed_reference_profiles Ref hdRef g0 R hGeom0
      (fun nu a => (hGCharts nu a).1) (fun nu a => (hGCharts nu a).2) hScompact
  obtain ⟨hOpen0,hGeomC0,Forward1,Inverse1,Meta1,hForward1,hInverse1,hMeta1,hProfilesC00⟩ :=
    round3_parameter_fixed_carrier_reference_profiles Ref hdRef g0 R hGeom0
      (fun nu a => (hGCharts nu a).1) (fun nu a => (hGCharts nu a).2) hScompact
  let ForwardC : ℕ → ℝ := fun j => max (Forward0 j) (Forward1 j)
  let InverseC : ℕ → ℝ := fun j => max (Inverse0 j) (Inverse1 j)
  let MetaC : ℕ → ℝ := fun j => max (Meta0 j) (Meta1 j)
  have hForwardC : ∀ j, 0 ≤ ForwardC j := fun j => (hForward0 j).trans (le_max_left _ _)
  have hInverseC : ∀ j, 0 ≤ InverseC j := fun j => (hInverse0 j).trans (le_max_left _ _)
  have hMetaC : ∀ j, 0 ≤ MetaC j := fun j => (hMeta0 j).trans (le_max_left _ _)
  have hProfiles0 := round4SpatialParameterOriginalChartProfiles_mono hProfiles00
    (fun j => le_max_left (Forward0 j) (Forward1 j))
    (fun j => le_max_left (Inverse0 j) (Inverse1 j))
    (fun j => le_max_left (Meta0 j) (Meta1 j))
  have hProfilesC0 := round4SpatialParameterOriginalChartProfiles_mono hProfilesC00
    (fun j => le_max_right (Forward0 j) (Forward1 j))
    (fun j => le_max_right (Inverse0 j) (Inverse1 j))
    (fun j => le_max_right (Meta0 j) (Meta1 j))
  have hNamed0 := round4_actual_original_chart_profiles_named_meta Ref hdRef hsRef hnRef
    BS0 TS0 BP0 TP0 Given hBS0 hTS0 hBP0 hTP0 Ds Dp B hChart RS RP hParameter packet profiles
    jet hFixed hFixedBound Forward0 Inverse0 Meta0 hProfiles00
  have hNamedC := round4SpatialParameterOriginalChartProfiles_mono hNamed0
    (fun j => le_max_left (Forward0 j) (Forward1 j))
    (fun j => le_max_left (Inverse0 j) (Inverse1 j)) (fun _ => le_rfl)
  refine ⟨packet,jet,profiles,epsilon,ForwardC,InverseC,MetaC,heps,hForwardC,hInverseC,hMetaC,hNamedC,?_⟩
  intro r budget hbudget
  let C := round4SpatialReferenceNormalProfile m d N radius hradius BS0 TS0 BP0 TP0
    InverseC ForwardC Given Ds Dp r budget profiles.cF profiles.cT
  obtain ⟨hC,hMake⟩ := round4_parameter_spatial_fixed_carrier_normal_stage
    (m := m) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 InverseC ForwardC MetaC Given hBS0 hTS0 hBP0 hTP0 hInverseC hForwardC hGiven
    Ds Dp radius hradius r budget (profiles.cF/16) (profiles.cT/16) (1/4)
    hbudget (div_pos profiles.cF_pos (by norm_num)) (div_pos profiles.cT_pos (by norm_num)) (by norm_num)
  refine ⟨hC,?_⟩
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
    Rparent hFullPart hCount ForwardC InverseC MetaC (fun p x => F (p,x)) hF stable hProfiles0
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

#print axioms round4_actual_spatial_parameter_geometric_named_meta_before_order
end GlobalEmbedding.Continuation
