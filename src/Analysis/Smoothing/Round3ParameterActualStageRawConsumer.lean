import Probes.Round3ParameterActualSecondaryFactory
import Smoothing.Round3OuterReferenceCanonicalConsumer
import Smoothing.Round3OuterStageDataProfiles
import Smoothing.Round3OuterActualParameterCanonicalMean

/-! The exact reference-family identity survives the actual admissible-stage
to canonical mean transition. This main consumer keeps the full result behind
an explicit proposition so the literal infinite-stage entrance can use it
without re-elaborating every native chart and germ proof. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal TensorProduct
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance outerStableMeanSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance outerStableMeanSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

private local instance outerStableMeanGeometryFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance outerStableMeanGeometryFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance outerStableMeanGeometryHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] Ey) := inferInstance
private local instance outerStableMeanGeometryHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] Ey) := inferInstance
private local instance outerStableMeanGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance outerStableMeanGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance
private local instance outerStableMeanGeometryT0Normed : NormedAddCommGroup (D →L[ℝ] Tdata) := inferInstance
private local instance outerStableMeanGeometryT0Space : NormedSpace ℝ (D →L[ℝ] Tdata) := inferInstance
private local instance outerStableMeanCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance outerStableMeanCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance outerStableMeanCjetNormed : NormedAddCommGroup (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance outerStableMeanCjetSpace : NormedSpace ℝ (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance outerStableMeanCANormed : NormedAddCommGroup
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance outerStableMeanCASpace : NormedSpace ℝ
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance outerStableMeanCBNormed : NormedAddCommGroup
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance outerStableMeanCBSpace : NormedSpace ℝ
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedSpace



private local instance outerStableArgumentLinearNormed : NormedAddCommGroup ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance outerStableArgumentLinearSpace : NormedSpace ℝ ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private local instance outerStableArgumentBilinearNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

private local instance coherentSignedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

abbrev Round3ParameterOriginalSecondaryIndex
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref) (hsRef : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (secondary : Round3PreparedParameterSecondaryPacket Ref hdRef hsRef theta) :=
  Sigma (fun r : ActualSecondarySignedRecord (Fin Ref.primaryCount) =>
    Sigma (fun i : Fin Ref.atlas.count × Fin Ref.parameterCount => ↥(secondary.s r i)))

def Round3ParameterActualCoherentConclusion
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref) (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hnRef : IncrementsOriginalFreeNormalConditions Ref hdRef hsRef)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hdRef hsRef theta packet)
    (secondary : Round3PreparedParameterSecondaryPacket Ref hdRef hsRef theta)
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm})
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {q : ℕ} {budget : ℝ} {reference Given : ℕ → ℝ}
    (stage : Round3RepairOriginalSmoothingStage
      (round3ParameterStageData Ref F H Ref.parameterOpen Ref.freeNormal Ref.primaryDomain neighborhood)
      BS0 TS0 BP0 TP0 Ds Dp radius hradius q budget reference Given)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => F (p,x)))
    (normal : Fin Ref.primaryCount → P × M → Ey)
    (Cnormal ForwardC InverseC MetaC Packet Mrest Cut Tinv Tobs : ℕ → ℝ)
    (R L : ℕ) (lower rho : ℝ) : Prop :=
    let g0 := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    let Data := round3ParameterStageData Ref F H Ref.parameterOpen Ref.freeNormal Ref.primaryDomain neighborhood
    ∃ rebound : Round3RepairNormalRebound stage normal domain Cnormal,
      let E := round3RepairRebindNormalData Data normal domain
      IncrementsOriginalSliceImmersionInputs E ∧
      IncrementsOriginalPhaseConditions E rebound.domain_conditions rebound.smooth_inputs ∧
      IncrementsOriginalCoordinateEllipticityInputs E (lower/4) ∧
    ∃ g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
        (Λ := Fin Ref.primaryCount) (Β := Round3ParameterWholePrimaryIndex Ref theta packet)
        (fun p x => F (p,x)),
      g.eta = (fun nu => round3FixedCarrierCutoff (g0.eta nu)) ∧
      (∀ nu a, ((g.chart nu a) : P × M → P × D) = g0.chart nu a) ∧
      (∀ nu a, ((g.chart nu a).symm : P × D → P × M) = (g0.chart nu a).symm) ∧
      Round3ParameterOriginalPrimaryGeometry E g R ∧
      Round3ParameterOriginalChartProfiles E g ForwardC InverseC MetaC ∧
      Round3ParameterOriginalGeneratedCanonicalSupply E hF g stage.samples_compact
        stage.ell (lower/4) (profiles.cT/16) rho (Packet 0) q R Packet ForwardC InverseC MetaC ∧
      Round3ParameterCoherentSecondaryOutput
        (SubSecondary := Round3ParameterOriginalSecondaryIndex Ref hdRef hsRef theta secondary)
        E (fun p x => F (p,x)) hF
        (round3Parameter_restrictPrimaryFamily (fun p x => F (p,x)) g univ isOpen_univ)
        q stage.ell univ Mrest Cut Tinv Tobs (L*5^Module.finrank ℝ (Ep × D))
        (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet)

theorem round3Parameter_uniform_actual_stage_raw_consumer
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref) (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hnRef : IncrementsOriginalFreeNormalConditions Ref hdRef hsRef)
    (hAll : Ref.parameterSet = univ) (hLinearRef : IncrementsOriginalLinearSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hdRef hsRef theta packet)
    (secondary : Round3PreparedParameterSecondaryPacket Ref hdRef hsRef theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M))
    (hPart : ∀ z, ∑ i, theta i z = 1) (R L : ℕ)
    (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ L)
    (BS0 TS0 BP0 TP0 reference Given Cnormal ForwardC InverseC MetaC Tinv Kcut Tobs : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hInverseC : ∀ j, 0 ≤ InverseC j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (q : ℕ) (budget lower : ℝ) :
    ∃ Cmap : ℕ → ℝ, (∀ j, 0 ≤ Cmap j) ∧
    ∃ Ctarget : ℕ → ℝ, (∀ j, 0 ≤ Ctarget j) ∧
    ∃ Mrest Cut : ℕ → ℝ, (∀ j, 0 ≤ Mrest j) ∧ (∀ j, Cut j=Kcut (actualSecondarySolveOrder q j)) ∧
    let Packet := fun j => max (Cmap j*budget)
      (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j)))
    ∀ (F : P × M → Ey)
      (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
    let Data := round3ParameterStageData Ref F H Ref.parameterOpen Ref.freeNormal Ref.primaryDomain neighborhood
    ∀ (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius q budget reference Given),
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius q budget reference Given stage) p
    ∀ normal : Fin Ref.primaryCount → P × M → Ey,
    let g0 := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    ∀ (actual : Round3OuterParameterAdmissibleStageOutput Ref hdRef hsRef hnRef theta packet profiles
      stage hF normal domain Cnormal ForwardC InverseC MetaC R lower)
      (rebound : Round3RepairNormalRebound stage normal domain Cnormal)
      (stable : ∀ r i (a : secondary.s r i), Round3PreparedParameterStableSecondaryPiece Ref hdRef hsRef i r _
        (secondary.piece r i a) (fun p x => F (p,x)) hF),
    let E := round3RepairRebindNormalData Data normal domain
    (∀ r i (a : secondary.s r i) observer,
      ∃ out : Round3PreparedParameterRawPiece E rebound.domain_conditions rebound.smooth_inputs (i.1,observer) r
        ((Ref.parameterChart observer).target ×ˢ (univ : Set M))
        (fun v : Fin Ref.atlas.count => Ref.atlas.chart v)
        (fun v => (parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
          Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet (v,observer)),
      out.choice = ((round3PreparedParameterSecondaryChoice Ref hdRef hsRef i r _ (stable r i a).piece).pullback
        (Ref.parameterChart observer)).toNative ∧
      out.Tinv=Tinv ∧ out.Kcut=Kcut ∧ out.Tobs=Tobs ∧
      out.cT=(secondary.piece r i a).cT/16 ∧ out.Bnative=1+Tobs 1) →
    IncrementsOriginalQualitativeDecompositionInputs Data →
    ∀ rho : ℝ, IncrementsOriginalDecompositionReserveInputs Data rho →
    Round3ParameterActualCoherentConclusion Ref hdRef hsRef hnRef theta packet profiles secondary F H neighborhood
      stage hF normal Cnormal ForwardC InverseC MetaC Packet Mrest Cut Tinv Tobs R L lower rho := by
  obtain ⟨Cmap,hCmap,Ctarget,hCtarget,hCanonical⟩ :=
    round3_uniform_reference_parameter_canonical_consumer
      (m := m) (d := d) (N := N) (M := M) (P := P)
      BS0 TS0 BP0 TP0 reference Given Cnormal ForwardC InverseC MetaC hBS0 hTS0 hBP0 hTP0 hInverseC
      Ds Dp radius hradius q budget lower
  obtain ⟨CmapS,hCmapS,CtargetS,hCtargetS,hBudget⟩ :=
    round3Outer_exists_uniform_parameterRound2_original_stage_data_profiles
      (n := m+1) (d := d) (N := N) (M := M) (P := P)
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius q
  let InputBudget := fun j => max (CmapS j*budget)
    (max (CtargetS j*budget+(j+1)*reference j) (max (Given j) (Cnormal j)))
  obtain ⟨Mrest,Cut,hMrest,hCut,hSecondary⟩ := round3Parameter_actual_coherent_secondary_factory
    Ref hdRef hsRef hAll theta secondary hSupport hPart L hCount q (lower/4) InputBudget Tinv Kcut Tobs
  refine ⟨Cmap,hCmap,Ctarget,hCtarget,Mrest,Cut,hMrest,hCut,?_⟩
  intro Packet F H neighborhood Data stage hF normal g0 domain actual rebound stable E hRaw hDecomp rho hReserve
  have canon := hCanonical Ref hdRef hsRef hnRef hAll hLinearRef theta packet profiles F H neighborhood
    stage normal R actual hDecomp rho hReserve
  obtain ⟨rebound',hImm,hPhase,hEll,g,hEta,hForward,hInverse,hGeom,hProfiles,hSupply,hPhysical⟩ := canon
  obtain ⟨Kt,hKt,hKtBound,hGiven⟩ := hBudget E budget reference
    (fun j => max (Given j) (Cnormal j)) rebound'.stage
  have hCoreFinite (j : ℕ) : incrementsOriginalCoreInputProfile E j stage.ell ≠ ⊤ := by
    have hf : actualOriginalGivenInputProfile E j stage.ell ≠ ⊤ := by
      rw [← rebound'.ell_eq]
      exact (hGiven j).1
    exact ne_top_of_le_ne_top hf (actualOriginalGivenInputProfile_core_le E j stage.ell)
  have hCoreBound (j : ℕ) : (incrementsOriginalCoreInputProfile E j stage.ell).toReal ≤ InputBudget j := by
    have hb : actualOriginalGivenInputProfile E j stage.ell ≠ ⊤ ∧
        (actualOriginalGivenInputProfile E j stage.ell).toReal ≤ InputBudget j := by
      rw [← rebound'.ell_eq]
      exact hGiven j
    exact (ENNReal.toReal_mono hb.1 (actualOriginalGivenInputProfile_core_le E j stage.ell)).trans hb.2
  have hJoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ F := by
    rw [← modelWithCornersSelf_prod]
    exact round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0
      Ds Dp radius hradius q budget reference Given stage
  have hSec := hSecondary Mrest (fun _ => le_rfl) (fun p x => F (p,x)) hF hJoint stable H Ref.parameterOpen
    normal domain neighborhood rebound'.domain_conditions rebound'.smooth_inputs hRaw stage.ell stage.ell_pos
    (stage.ell_le_t.trans stage.t_le_one) hEll hCoreFinite hCoreBound
    (Round3ParameterWholePrimaryIndex Ref theta packet) (fun a => a.1.1)
    (round3Parameter_restrictPrimaryFamily (fun p x => F (p,x)) g univ isOpen_univ)
    (fun nu => congrFun hGeom.phase nu) (fun nu => congrFun hGeom.cutoff nu) hPhysical
  exact ⟨rebound',hImm,hPhase,hEll,g,hEta,hForward,hInverse,hGeom,hProfiles,hSupply,hSec⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_uniform_actual_stage_raw_consumer
