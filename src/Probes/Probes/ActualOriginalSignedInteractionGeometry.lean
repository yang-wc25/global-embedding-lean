import Probes.ActualSecondaryConstructedHostGeometry
import Probes.ActualOriginalSignedCarrierConditioning
import Probes.ActualRelativeInteractionCarrier

/-! Complete secondary RawGeometry on the TRUE effective interaction carrier.
The ordinary partition rho may extend outside the closed primary support pair.
Its effective carrier is tsupport(rho) intersected with the TWO actual relative
primary supports. Original Good is used only there. Compactness, original
support transport and relative closedness are constructed internally. The
same chart, cutoff and scalar phase functions are never altered. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Bundle
open scoped ContDiff Topology BigOperators TensorProduct ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance marginSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance marginSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ}
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

variable {P : Type*} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

private local instance adaptedGeometryFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryT0Normed : NormedAddCommGroup (D →L[ℝ] Tdata) := inferInstance
private local instance adaptedGeometryT0Space : NormedSpace ℝ (D →L[ℝ] Tdata) := inferInstance
private local instance marginCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance marginCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance marginCjetNormed : NormedAddCommGroup (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCjetSpace : NormedSpace ℝ (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance marginCANormed : NormedAddCommGroup
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCASpace : NormedSpace ℝ
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance marginCBNormed : NormedAddCommGroup
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCBSpace : NormedSpace ℝ
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedSpace

def actualOriginalParameterSupportPair
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (nu mu : Fin Data.primaryCount) (W : Set (Ep × M)) : Set (Ep × M) :=
  incrementsGlobalRelativeSupport W
    (fun z => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)) ∩
  incrementsGlobalRelativeSupport W
    (fun z => Data.cutoff mu ((Data.parameterChart i.2).symm z.1,z.2))

theorem actual_original_signed_interaction_raw_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b
      (actualOriginalParameterSignedPhase Data i r.val) e)
    (rho : Ep × M → ℝ) (hCompact : IsCompact (tsupport rho))
    (hSupport : tsupport rho ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source)
    (hsource : b.source ⊆ actualOriginalNativeOpen Data i)
    (hactive : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Data ∧
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Data)
    (Vprep : Set (Ep × M))
    (hVprep : (actualHostAdaptedChart (Data.atlas.chart i.1) b).source ⊆ Vprep)
    (hVParam : ∀ w ∈ Vprep, w.1 ∈ (Data.parameterChart i.2).target)
    (hVOriginal : MapsTo (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2))
      Vprep (incrementsOriginalParameterRegion Data)) :
    let carrier := tsupport rho ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 Vprep
    ∃ (cT : ℝ) (b' : OpenPartialHomeomorph X X)
      (e' : Ep → OpenPartialHomeomorph M D),
      0 < cT ∧ b'.source ⊆ b.source ∧ b'.target ⊆ b.target ∧
      (b' : X → X) = b ∧ (b'.symm : X → X) = b.symm ∧
      (∀ p, ((e' p).symm : D → M) = (e p).symm) ∧
      IsCompact carrier ∧ carrier ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) b').source ∧
      ∀ (n j : ℕ) (T : ℕ → ℝ), (∀ k, 0 ≤ T k) → ∀
      (S : Set X), S ⊆ b'.target →
      MapsTo b.symm S ((parameterTensorModelEquiv (m+1) d) ⁻¹'
        incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet i) → ∀
      (ell budget c Bnative : ℝ), 0 < ell → ell ≤ 1 →
      IncrementsOriginalCoordinateEllipticityInputs Data c → 0 < Bnative →
      incrementsOriginalCoreInputProfile Data (max n j) ell ≠ ⊤ →
      (incrementsOriginalCoreInputProfile Data (max n j) ell).toReal ≤ budget →
      (∀ z ∈ b.source, ‖fderiv ℝ b z‖ ≤ Bnative) →
      (∀ k, 1 ≤ k → k ≤ max n j+2 → ∀ z ∈ S,
        ell^(k-1)*‖iteratedFDeriv ℝ k b.symm z‖ ≤ T k) →
      let F := actualOriginalOpenParameterSlice Data i
      let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
      let Cmap := actualOriginalMapJetCost (m+1) d N (max n j)*budget
      let Mg := actualAdaptedUniformGeometryCost m N (max n j) T c cT Bnative Cmap Cmap
      ∃ out : ActualSecondaryRawGeometry F hF n j ell Mg Vprep,
        out.c = (fun p x => (e' p).symm x) ∧
        out.chart = actualHostAdaptedChart (Data.atlas.chart i.1) b' ∧
        out.phase = actualOriginalParameterSignedPhase Data i r.val ∧
        out.sample = S ∧ out.support = carrier ∧ out.spatialChart = e' := by
  intro carrier
  let pull : Ep × M → P × M := fun z => ((Data.parameterChart i.2).symm z.1,z.2)
  have hPull : ContinuousOn pull Vprep :=
    ((Data.parameterChart i.2).symm.continuousOn.comp continuous_fst.continuousOn hVParam).prodMk
      continuous_snd.continuousOn
  have hOriginal (nu : Fin Data.primaryCount) :
      incrementsGlobalRelativeSupport Vprep (fun z => Data.cutoff nu (pull z)) ⊆
        pull ⁻¹' incrementsOriginalRelativeCutoffSupport Data nu :=
    actual_relative_support_pullback_subset Vprep (incrementsOriginalParameterRegion Data)
      pull hPull hVOriginal (Data.cutoff nu)
  have hCarrierCompact : IsCompact carrier :=
    actual_compact_interaction_carrier (tsupport rho) Vprep hCompact (hSupport.trans hVprep)
      (fun z => Data.cutoff r.val.1.1 (pull z)) (fun z => Data.cutoff r.val.1.2 (pull z))
  have hCarrierSource : carrier ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source :=
    inter_subset_left.trans hSupport
  have hPair : ∀ w ∈ carrier, pull w ∈
      incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
        incrementsOriginalRelativeCutoffSupport Data r.val.1.2 :=
    fun w hw => ⟨hOriginal r.val.1.1 hw.2.1,hOriginal r.val.1.2 hw.2.2⟩
  have hCarrierClosed : IsClosed (Subtype.val ⁻¹' carrier : Set Vprep) :=
    ((isClosed_tsupport rho).preimage continuous_subtype_val).inter
      ((actual_relative_support_preimage_closed Vprep (fun z => Data.cutoff r.val.1.1 (pull z))).inter
        (actual_relative_support_preimage_closed Vprep (fun z => Data.cutoff r.val.1.2 (pull z))))
  obtain ⟨cF,cT,b',e',hcF,hcT,hSource,hTarget,hb,hbi,hdata',hSupport',hASource,hInverse,hFb,hTb⟩ :=
    actual_original_signed_carrier_conditioned_chart Data hd hs hp hImm i r b e hdata
      carrier hCarrierCompact hCarrierSource hsource hactive hPair
  refine ⟨cT,b',e',hcT,hSource,hTarget,hb,hbi,hInverse,hCarrierCompact,hSupport',?_⟩
  intro n j T hT S hS hsample ell budget c Bnative hell hell1 hEll hBnative hfinite hbudget hnative hinvjet
  apply actual_secondary_geometry_from_constructed_host Data hd hs hImm i r.val.1.1 b' e'
    (actualOriginalParameterSignedPhase Data i r.val) hdata' carrier Vprep hCarrierClosed
    hSupport' (hASource.trans hVprep) (hSource.trans hsource) n j T hT S hS
    (by simpa only [hbi] using hsample) ell budget c cT Bnative hell hell1 hEll hcT hBnative
    hfinite hbudget ?_ hTb ?_
  · intro z hz
    rw [hb]
    exact hnative z (hSource hz)
  · intro k hk hkj z hz
    rw [hbi]
    exact hinvjet k hk hkj z hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_signed_interaction_raw_geometry
