import Probes.Round3ParameterOriginalCoreActiveGeometry
import Probes.ActualSecondaryQuadraticConstruction

/-! Actual secondary geometry needs the first native derivative only on the
genuine inverse image of the actual sample. No whole observer-chart bound
is imposed, so this applies to nonlinear parameter-chart conjugation.

The original Core and actual produced chart data construct the complete
secondary geometry record consumed by the finite-increment theorem. The
phase may be any actual signed secondary phase: no primary-only substitution
is used. All true-B/J/A/B/value/inverse smoothness and bounds are outputs.
The displayed native frame reserve is supplied by the actual conditioned
packet construction; it is not a bound on a solver output. -/

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

theorem round3Parameter_secondary_geometry_from_active_original_core
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (n j : ℕ) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (chart : OpenPartialHomeomorph (Ep × M) X)
    (phase : Ep × M → ℝ) (S : Set X) (support W : Set (Ep × M))
    (sourceOpen : Set X) (hOpen : IsOpen sourceOpen)
    (hSU : S ⊆ chart.target) (hSupportClosed : IsClosed (Subtype.val ⁻¹' support : Set W))
    (hSupportSource : support ⊆ chart.source) (hSourceDomain : chart.source ⊆ W)
    (hChart : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ chart chart.source)
    (hInverse : ∀ z ∈ chart.target, chart.symm z = (z.1,(e z.1).symm z.2))
    (hPhase : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ phase chart.source)
    (hAdapt : ∀ y ∈ chart.source, phase y = (chart y).2 0)
    (hWO : sourceOpen ⊆ actualOriginalNativeOpen Data i)
    (hcoord : ∀ z ∈ chart.target, z.2 ∈ (e z.1).target ∧
      (e z.1).symm z.2 ∈ (Data.atlas.chart i.1).source)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition (fun _ => Data.atlas.chart i.1) e) chart.target)
    (hback : ContDiffOn ℝ ∞ (actualSourceChartTransition e (fun _ => Data.atlas.chart i.1)) sourceOpen)
    (hmap : MapsTo (actualSourceChartTransition (fun _ => Data.atlas.chart i.1) e) chart.target sourceOpen)
    (hsample : MapsTo (actualSourceChartTransition (fun _ => Data.atlas.chart i.1) e) S
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Data.atlas
        Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (ell budget c cT backBound : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (hcT : 0 < cT) (hBackPos : 0 < backBound)
    (hfinite : incrementsOriginalCoreInputProfile Data (max n j) ell ≠ ⊤)
    (hbudget : (incrementsOriginalCoreInputProfile Data (max n j) ell).toReal ≤ budget)
    (hBackBound : ∀ z ∈ (actualSourceChartTransition
        (fun _ => Data.atlas.chart i.1) e) '' S,
      ‖fderiv ℝ (actualSourceChartTransition e (fun _ => Data.atlas.chart i.1)) z‖ ≤ backBound)
    (hReserve : ∀ z ∈ chart.target, ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame
        (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
        (e z.1).symm z.2 v‖^2)
    (hJets : ∀ k, 1 ≤ k → k ≤ max n j+2 → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k
        (actualSourceChartTransition (fun _ => Data.atlas.chart i.1) e) z‖ ≤ T k) :
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let Cmap := actualOriginalMapJetCost (m+1) d N (max n j)*budget
    let Mg := actualAdaptedUniformGeometryCost m N (max n j) T c cT backBound Cmap Cmap
    ∃ out : ActualSecondaryRawGeometry F hF n j ell Mg W,
      out.c = (fun p x => (e p).symm x) ∧ out.chart = chart ∧ out.phase = phase ∧
      out.sample = S ∧ out.support = support ∧ out.spatialChart = e := by
  intro F hF Cmap Mg
  obtain ⟨hImmersion,hGram,hG,hJ,hT0,hBR,hA,hB⟩ :=
    round3Parameter_original_core_active_geometry T hT (max n j) Data hd hs hImm i nu e he
      chart.target sourceOpen S chart.open_target hOpen hSU hWO hcoord hphi hback hmap hsample
      ell budget c cT backBound hell hell1 hEll hcT hBackPos hfinite hbudget hBackBound hReserve hJets
  let out : ActualSecondaryRawGeometry F hF n j ell Mg W := {
    c := fun p x => (e p).symm x
    chart := chart
    sample := S
    sample_subset := hSU
    support := support
    support_closed := hSupportClosed
    support_source := hSupportSource
    source_domain := hSourceDomain
    chart_smooth := hChart
    inverse := hInverse
    phase := phase
    phase_smooth := hPhase
    adaptation := hAdapt
    brows_smooth := hBR.1
    inverse_smooth := hG.1
    transverse_smooth := hJ.1
    value_smooth := hT0.1
    coefficientA_smooth := hA.1
    coefficientB_smooth := hB.1
    brows_bound := fun k hk z hz => hBR.2 k (hk.trans (le_max_left n j)) z hz
    transverse_bound := fun k hk z hz => hJ.2 k (hk.trans (le_max_left n j)) z hz
    inverse_bound := fun k hk z hz => hG.2 k (hk.trans (le_max_right n j)) z hz
    value_bound := fun k hk z hz => hT0.2 k (hk.trans (le_max_right n j)) z hz
    coefficientA_bound := fun k hk z hz => hA.2 k (hk.trans (le_max_left n j)) z hz
    coefficientB_bound := fun k hk z hz => hB.2 k (hk.trans (le_max_left n j)) z hz
    spatialChart := e
    coordinate := rfl
    maximal := he
    target := fun z hz => (hcoord z hz).1
    immersion := hImmersion
    gram := hGram }
  exact ⟨out,rfl,rfl,rfl,rfl,rfl,rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_geometry_from_active_original_core
