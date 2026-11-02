import Repair.EntranceObserverBudget
import Smoothing.Round4SpatialParameterGeometryBeforeOrder
import Smoothing.Round4ReferenceFactoryProfiles
import Smoothing.Round4WholeOriginalMeta
import Smoothing.Round3OuterOriginalParameterGeometricFactory
import Smoothing.Round4SpatialParameterFixedCarrierNormalStage
import Smoothing.Round4SpatialReferenceNormalProfile

/-!
# The complete actual normal stage consumes numerical observer profiles

The same selected primary packet and numerical reference profiles now
supply the actual original observer Forward/Inverse through primitive
atlas-transition budgets. The fixed-carrier plateau retains these same
functions and costs. Only its cutoff-jet certificate remains qualitative;
it does not enter the named normal or repair costs. The ordinary cutoff Meta profile is supplied by the actual scalar-cutoff
construction directly. The obsolete one-phase native-chart jet interface
is absent: transverse chart coordinates may be genuine atlas transitions.
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

/-- The literal ordinary cutoff in each actual observed adapted chart.
This is a primitive scalar-cutoff certificate, independent of the map
increment, mean solution, smoothing stage, state or repair output. -/
def RepairOriginalPrimaryCutoffJets
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {Sub : Type*} [Fintype Sub]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Ref.primaryCount) (Β := Sub)
      (fun p x => Ref.F (p,x))) (Meta : ℕ → ℝ) : Prop :=
  ∀ nu a i,
    let gN := round3ParameterNativePrimary (fun p x => Ref.F (p,x)) g (Ref.parameterChart i.2)
    let t := ((OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart i.1)).symm.trans (gN.chart nu a)
    let etaN := fun z : Ep × D => gN.eta nu a ((gN.chart nu a).symm z)
    ∀ k z, parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet i →
      ((Ref.parameterChart i.2).symm z.1,(Ref.atlas.chart i.1).symm z.2) ∈ tsupport (g.eta nu a) →
      ‖iteratedFDeriv ℝ k etaN (t z)‖ ≤ Meta k

theorem repairEntrance_original_profiles_with_direct_cutoff
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {Sub : Type*} [Fintype Sub]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Ref.primaryCount) (Β := Sub)
      (fun p x => Ref.F (p,x))) (Forward Inverse OldMeta Meta : ℕ → ℝ)
    (old : Round3ParameterOriginalChartProfiles Ref g Forward Inverse OldMeta)
    (cutoff : RepairOriginalPrimaryCutoffJets Ref g Meta) :
    Round3ParameterOriginalChartProfiles Ref g Forward Inverse Meta := by
  intro ell hell hell1 nu a i gN t etaN k z hz hPhysical
  have hh := old ell hell hell1 nu a i k z hz hPhysical
  refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,?_⟩
  exact ((mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)).trans_eq
    (one_mul _)).trans (cutoff nu a i k z hz hPhysical)

theorem repairEntrance_direct_meta_geometric_before_order
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
    ∀ (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref hdRef hsRef theta packet)
      (observer : RepairPrimaryObserverBudget Ref hdRef hsRef theta packet profiles)
      (NumericMeta : ℕ → ℝ) (hNumericMeta : ∀ j, 0 ≤ NumericMeta j)
      (cutoff : RepairOriginalPrimaryCutoffJets Ref
        (round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
          (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)) NumericMeta)
      (epsilon : ℝ) (hepsilon : 0 < epsilon)
      (hStable : ∀ (F : P → M → Ey)
        (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
        (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p)),
        let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
          Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
        paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
          (fun z => F z.1 z.2-Ref.F z))
          (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ →
        (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
          (fun z => F z.1 z.2-Ref.F z))
          (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ epsilon →
        Nonempty (Round3ParameterWholeStableReference Ref hdRef hsRef theta packet profiles F hF)),
    let g0 := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    ∃ (ForwardC InverseC MetaC : ℕ → ℝ),
      ForwardC = observer.forwardProfile ∧ InverseC = observer.inverseProfile ∧
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
  intro theta packet profiles observer NumericMeta hNumericMeta cutoff epsilon heps hStable
  have hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hdRef.parameter_charts_smooth
  have hQT : ∀ i, Ref.parameterNormDomain i ⊆ (B.chart i).target := by
    rw [hChart]
    exact hdRef.parameter_norm_subset
  obtain ⟨W0,hW0,hKW0,hSmooth0,hCompact0,hSupport0,hPart0,hCount0⟩ :=
    round3Parameter_actual_compact_product_parents BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp
      Ref.atlas B hdRef.atlas_smooth hB Ref.parameterSet RS RP Ref.sourceNormDomain Ref.parameterNormDomain
      hOmega hQ hdRef.source_norm_subset hQT hSource hParameter
  have hGeom0 := round3Parameter_whole_primary_family_geometry Ref hdRef hsRef hnRef theta
    (packet.replacePieces Ref theta profiles.piece profiles.host profiles.cutoff)
    (fun z => hPart0 z (hKW0 (by rw [hAll]; exact mem_univ _))) _ hCount0
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
  let ForwardC := observer.forwardProfile
  let InverseC := observer.inverseProfile
  let MetaC : ℕ → ℝ := fun j => max (Meta0 j) (Meta1 j)
  have hForwardC : ∀ j, 0 ≤ ForwardC j := observer.forward_nonneg
  have hInverseC : ∀ j, 0 ≤ InverseC j := observer.inverse_nonneg
  have hMetaC : ∀ j, 0 ≤ MetaC j := fun j => (hMeta0 j).trans (le_max_left _ _)
  have hNumerical := observer.original_profiles hnRef Forward0 Inverse0 Meta0 hProfiles00
  have hNumericalCarrier := repairEntrance_fixed_carrier_inherits_observer_profiles Ref g0 hOpen0
    ForwardC InverseC Meta0 Forward1 Inverse1 Meta1 hNumerical hProfilesC00
  have hProfiles0 := round4SpatialParameterOriginalChartProfiles_mono hNumerical
    (fun _ => le_rfl) (fun _ => le_rfl) (fun j => le_max_left (Meta0 j) (Meta1 j))
  have hProfilesC0 := round4SpatialParameterOriginalChartProfiles_mono hNumericalCarrier
    (fun _ => le_rfl) (fun _ => le_rfl) (fun j => le_max_right (Meta0 j) (Meta1 j))
  have hNamed0 := repairEntrance_original_profiles_with_direct_cutoff Ref g0
    ForwardC InverseC Meta0 NumericMeta hNumerical cutoff
  refine ⟨ForwardC,InverseC,MetaC,rfl,rfl,heps,hForwardC,hInverseC,hMetaC,hNamed0,?_⟩
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

#print axioms repairEntrance_direct_meta_geometric_before_order
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_original_profiles_with_direct_cutoff
