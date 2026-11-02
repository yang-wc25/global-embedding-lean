import Smoothing.Round4LocalPrimaryReferenceConsumer
import Smoothing.Round4LocalPrimaryNamedMetaCanonicalMean
import Smoothing.Round4LocalPrimaryActualCanonicalMean

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

theorem round4Parameter_named_meta_reference_canonical_consumer
    (BS0 TS0 BP0 TP0 reference Given Cnormal ForwardC InverseC MetaC GeometryMeta : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hInverseC : ∀ j, 0 ≤ InverseC j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (q : ℕ) (budget lower : ℝ) :
    let Cmap := fun j => round4PreparedPairConstant (m+1) d radius hradius BS0 TS0 BP0 TP0 Ds Dp j q
    let Ctarget := Cmap
    (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Ctarget j) ∧
    let Packet := fun j => max (Cmap j*budget)
      (max (Ctarget j*budget+(j+1)*reference j) (max (Given j) (Cnormal j)))
    ∀ (Ref : IncrementsOriginalNativeData (m+1) d N M P)
      (hdRef : IncrementsOriginalDomainConditions Ref) (hsRef : IncrementsOriginalSmoothInputs Ref)
      (hnRef : IncrementsOriginalFreeNormalConditions Ref hdRef hsRef)
      (hAll : Ref.parameterSet = univ) (hLinearRef : IncrementsOriginalLinearSmoothInputs Ref)
      (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
      (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
      (profiles : Round3ParameterWholeReferenceProfiles Ref hdRef hsRef theta packet)
      (F : P × M → Ey)
      (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
    let Data := round3ParameterStageData Ref F H Ref.parameterOpen Ref.freeNormal Ref.primaryDomain neighborhood
    ∀ (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius q budget reference Given),
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius q budget reference Given stage) p
    ∀ (normal : Fin Ref.primaryCount → P × M → Ey) (R Lprimary : ℕ)
      (hLocal : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Ref.cutoff nu))).card ≤ Lprimary),
    let g0 := round3ParameterWholePrimaryFamily Ref hdRef hsRef hnRef theta
      (round3OuterReferencePrimaryPacket Ref hdRef hsRef theta packet profiles)
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    Round3ParameterOriginalChartProfiles Ref g0 ForwardC InverseC MetaC →
    Round3OuterParameterAdmissibleStageOutput Ref hdRef hsRef hnRef theta packet profiles
      stage hF normal domain Cnormal ForwardC InverseC GeometryMeta R lower →
    IncrementsOriginalQualitativeDecompositionInputs Data →
    ∀ rho : ℝ, IncrementsOriginalDecompositionReserveInputs Data rho →
    Round4LocalPrimaryReferenceCanonicalConclusion Ref hdRef hsRef hnRef theta packet profiles F H neighborhood
      stage hF normal Cnormal ForwardC InverseC MetaC Packet R Lprimary lower rho := by
  intro Cmap Ctarget
  obtain ⟨hCmap,hCtarget,hMeanFactory⟩ :=
    round4_local_primary_named_meta_canonical_mean_from_stable
      (m := m) (d := d) (N := N) (M := M) (P := P)
      BS0 TS0 BP0 TP0 reference Given Cnormal ForwardC InverseC GeometryMeta MetaC hBS0 hTS0 hBP0 hTP0 hInverseC
      Ds Dp radius hradius q budget (lower/4)
  refine ⟨hCmap,hCtarget,?_⟩
  intro Packet Ref hdRef hsRef hnRef hAll hLinearRef theta packet profiles F H neighborhood Data stage hF
    normal R Lprimary hLocal g0 domain hNamed actual hDecomp rho hReserve
  obtain ⟨stable,hOpen,hGeom,hProfiles,rebound,hImm,hPrimary,hPhase,hEll⟩ := actual
  have hSame := round3_stable_primary_global_functions Ref hdRef hsRef hnRef theta packet profiles
    (fun p x => F (p,x)) hF stable
  have hNamedStable := round3Parameter_original_profiles_stage_rebase Ref hdRef g0
    ForwardC InverseC MetaC hNamed Ref.F Ref.H Ref.parameterOpen Ref.freeNormal
    Ref.primaryDomain Ref.tensorNeighborhood _ _ hGeom hSame.1 hSame.2.1 hSame.2.2.1
  have hMF := hMeanFactory Ref hdRef hsRef hnRef hAll hLinearRef theta packet profiles F H neighborhood
    stage stable R Lprimary hGeom hLocal hOpen hProfiles hNamedStable normal
  rw [hSame.1] at hMF
  obtain ⟨g,hEta,hForward,hInverse,hGeomNew,hProfilesNew,hCanonical,hPhysical⟩ :=
    hMF rebound hImm hPhase hEll hDecomp rho hReserve
  refine ⟨rebound,hImm,hPhase,hEll,g,?_,?_,?_,hGeomNew,⟨GeometryMeta,hProfilesNew⟩,hCanonical,hPhysical⟩
  · have hCut := congrArg
      (fun eta : Fin Ref.primaryCount → Round3ParameterWholePrimaryIndex Ref theta packet → P × M → ℝ =>
        fun nu => round3FixedCarrierCutoff (eta nu)) hSame.1
    exact hEta.trans hCut
  · exact fun nu a => (hForward nu a).trans (hSame.2.1 nu a)
  · exact fun nu a => (hInverse nu a).trans (hSame.2.2.1 nu a)

#print axioms round4Parameter_named_meta_reference_canonical_consumer
end GlobalEmbedding.Continuation
