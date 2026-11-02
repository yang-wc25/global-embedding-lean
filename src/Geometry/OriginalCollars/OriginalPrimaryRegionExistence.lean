import OriginalIncrements.OriginalPrimaryCompactReserve
import OriginalCollars.FactoryCommonGeometryPacket
import Probes.Round3PreparedPrimaryPhase

/-! Actual primary low geometry and the original chosen-phase kernel margin
on the SAME genuine construction region, produced for each fixed original
parent. No whole-primary-domain reserve, chart inverse or solver is input.
The physical parameter-open requirement is only on the parent support. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology TensorProduct Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements
open OriginalCollars
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance primaryRegionRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance primaryRegionSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [T2Space M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓙

private theorem original_parent_primary_carrier_active
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (hCompact : ∀i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    let K := originalNativePrimaryCarrier Data i nu
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
    IsCompact K ∧ K⊆actualOriginalPrimaryNativeOpen Data nu i := by
  intro K
  let thetaN := round3ParameterNativeParent (Data.parameterChart i.2) (theta i)
  let W := (Data.parameterChart i.2).target ×ˢ (univ : Set M)
  let pull : Ep × M → P × M := fun z=>((Data.parameterChart i.2).symm z.1,z.2)
  have hW : IsOpen W := (Data.parameterChart i.2).open_target.prod isOpen_univ
  have hN := round3Parameter_native_compact_parent (Data.parameterChart i.2)
    (hd.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth i)
    (fun z hz=>⟨(hSupport i hz).1.1,mem_univ _⟩)
  have hNSupport : tsupport thetaN ⊆ (Data.parameterChart i.2).target ×ˢ (Data.atlas.chart i.1).source := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := hN.2.2 hy
    exact ⟨(Data.parameterChart i.2).map_source (hSupport i hz).1.1,
      Data.atlas.inner_subset i.1 (hSupport i hz).2⟩
  have hOriginal : ∀y∈tsupport thetaN, pull y∈incrementsOriginalParameterRegion Data := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := hN.2.2 hy
    change ((Data.parameterChart i.2).symm ((Data.parameterChart i.2) z.1),z.2)∈_
    rw [(Data.parameterChart i.2).left_inv (hSupport i hz).1.1]
    exact ⟨(hSupport i hz).1.2,mem_univ _⟩
  have hPull : ContinuousOn pull W :=
    ((Data.parameterChart i.2).symm.continuousOn.comp continuous_fst.continuousOn
      (fun z hz=>hz.1)).prodMk continuous_snd.continuousOn
  let Wp := W ∩ pull ⁻¹' incrementsOriginalParameterRegion Data
  have hWp : IsOpen Wp := hPull.isOpen_inter_preimage hW (hd.parameter_open.prod isOpen_univ)
  refine ⟨originalNativePrimaryCarrier_isCompact Data i nu thetaN hN.2.1 hNSupport,?_⟩
  rintro z ⟨y,hy,rfl⟩
  have hySupport : y∈incrementsGlobalRelativeSupport Wp (fun w=>Data.cutoff nu (pull w)) := by
    rw [parameterRound2_global_relativeSupport_eq Wp hWp]
    have hyOld := (parameterRound2_global_relativeSupport_eq W hW
      (fun w=>Data.cutoff nu (pull w))) ▸ hy.2
    exact ⟨⟨hyOld.1,hOriginal y hy.1⟩,hyOld.2⟩
  have hOriginalCutoff : pull y∈incrementsOriginalRelativeCutoffSupport Data nu :=
    actual_relative_support_pullback_subset Wp (incrementsOriginalParameterRegion Data)
      pull (hPull.mono inter_subset_left) (fun w hw=>hw.2) (Data.cutoff nu) hySupport
  have hActive : pull y∈Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data :=
    ⟨hd.cutoff_support_local nu hOriginalCutoff,
      incrementsOriginalRelativeCutoffSupport_subset Data nu hOriginalCutoff⟩
  apply round3_prepared_native_primary_mem Data i nu _
    ((Data.atlas.chart i.1).map_source (hNSupport hy.1).2) (hNSupport hy.1).1
  change ((Data.parameterChart i.2).symm y.1,
    (Data.atlas.chart i.1).symm ((Data.atlas.chart i.1) y.2))∈_
  rw [(Data.atlas.chart i.1).left_inv (hNSupport hy.1).2]
  exact hActive

/-- Per-primary genuine low geometry on the actual original carrier.
Every witness precedes every later derivative order and oscillation scale. -/
theorem original_parent_primary_regions_exist
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (hCompact : ∀i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) :
    ∀ (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount),
    ∃ (mu Mb R buffer kernel : ℝ) (O : Set X),
      0<mu ∧ 0≤Mb ∧ 0<R ∧ 0<buffer ∧ 0<kernel ∧ IsOpen O ∧
      O⊆actualOriginalPrimaryNativeOpen Data nu i ∧
      (originalNativePrimaryCarrier Data i nu
        (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ⊆ closedBall 0 R) ∧
      (∀z∈originalNativePrimaryCarrier Data i nu
        (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)), ball z buffer⊆O) ∧
      (∀z∈originalNativePrimaryCarrier Data i nu
        (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)),
        mu≤‖(fderiv ℝ (originalNativePrimaryPhase Data nu i) z).comp (ContinuousLinearMap.inr ℝ Ep D)‖) ∧
      (∀z∈O, ‖fderiv ℝ (originalNativePrimaryPhase Data nu i) z‖≤Mb) ∧
      (∀z∈O, buffer*‖iteratedFDeriv ℝ 2 (originalNativePrimaryPhase Data nu i) z‖≤Mb) ∧
      (∀z∈O, ∀v, kernel*‖v‖ ≤ ‖covectorRestriction
        (round4ActualPhaseOperatorInChart
          (fun p x=>Data.F ((Data.parameterChart i.2).symm p,x))
          (fun _=>Data.atlas.chart i.1) z)
        (fderiv ℝ (fun x : D => Data.phase nu
          ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm x)) z.2) v‖) := by
  intro nu i
  let K := originalNativePrimaryCarrier Data i nu
    (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
  obtain ⟨hK,hKActive⟩ := original_parent_primary_carrier_active Data hd theta hCompact hSmooth hSupport nu i
  obtain ⟨kernel,U,hKernel,hU,hKU,hUActive,hRestriction⟩ :=
    original_primary_compact_reserve Data hd hs hp hImm i nu K hK hKActive
  obtain ⟨mu,Mb,R,buffer,O,hMu,hMb,hR,hBuffer,hO,hKO,hOU,hRadius,hBufferO,hPhase,hNoncrit,hFirst,hSecond⟩ :=
    round3_actual_original_primary_phase_preparation Data hd hs hp i nu K U hK hU hKU hUActive
  exact ⟨mu,Mb,R,buffer,kernel,O,hMu,hMb,hR,hBuffer,hKernel,hO,hOU.trans hUActive,
    hRadius,hBufferO,hNoncrit,hFirst,hSecond,fun z hz=>hRestriction z (hOU hz)⟩

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_parent_primary_regions_exist
