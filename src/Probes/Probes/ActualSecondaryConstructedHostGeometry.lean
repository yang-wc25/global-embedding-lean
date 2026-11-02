import Probes.ActualSecondaryOriginalCoreGeometry
import Probes.ActualIncrementHostGeometryInputs

/-! Construct the complete actual secondary geometry record from a real
phase-adapted host chart. All spatial transitions, native inverse identities,
smoothness and adaptation are read from that chart's actual slice data.
Only original Core values and the produced chart's native jets enter estimates. -/

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

theorem actual_secondary_geometry_from_constructed_host
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M D)
    (phase : Ep × M → ℝ)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b phase e)
    (support W : Set (Ep × M))
    (hSupportClosed : IsClosed (Subtype.val ⁻¹' support : Set W))
    (hSupportSource : support ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source)
    (hSourceDomain : (actualHostAdaptedChart (Data.atlas.chart i.1) b).source ⊆ W)
    (hsource : b.source ⊆ actualOriginalNativeOpen Data i)
    (n j : ℕ) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (S : Set X) (hS : S ⊆ b.target)
    (hsample : MapsTo b.symm S ((parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i))
    (ell budget c cT Bnative : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (hcT : 0 < cT) (hBnative : 0 < Bnative)
    (hfinite : incrementsOriginalCoreInputProfile Data (max n j) ell ≠ ⊤)
    (hbudget : (incrementsOriginalCoreInputProfile Data (max n j) ell).toReal ≤ budget)
    (hnative : ∀ z ∈ b.source, ‖fderiv ℝ b z‖ ≤ Bnative)
    (hTreserve : ∀ z ∈ b.target, ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame
        (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
        (e z.1).symm z.2 v‖^2)
    (hinvjet : ∀ k, 1 ≤ k → k ≤ max n j+2 → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k b.symm z‖ ≤ T k) :
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let Cmap := actualOriginalMapJetCost (m+1) d N (max n j)*budget
    let Mg := actualAdaptedUniformGeometryCost m N (max n j) T c cT Bnative Cmap Cmap
    ∃ out : ActualSecondaryRawGeometry F hF n j ell Mg W,
      out.c = (fun p x => (e p).symm x) ∧
      out.chart = actualHostAdaptedChart (Data.atlas.chart i.1) b ∧
      out.phase = phase ∧ out.sample = S ∧ out.support = support ∧ out.spatialChart = e := by
  intro F hF Cmap Mg
  let c0 := Data.atlas.chart i.1
  let a := actualHostAdaptedChart c0 b
  obtain ⟨hNativeHost,hb,hbi,hcoord,hphi,hback,hmap,hadapt⟩ :=
    actual_host_slice_geometry_inputs c0 (hd.atlas_smooth.chart_mem i.1) b phase e hdata
  obtain ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hbackEq,hforwardEq,hbackJets,hforwardJets⟩ := hdata
  have haTarget : a.target = b.target := hat
  have hSa : S ⊆ a.target := by rwa [hat]
  have hbackBound : ∀ z ∈ ((parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i) ∩ b.source,
      ‖fderiv ℝ (actualSourceChartTransition e (fun _ => c0)) z‖ ≤ Bnative := by
    intro z hz
    have heq := congrArg norm (hforwardJets 1 z hz.2)
    simp only [norm_iteratedFDeriv_one] at heq
    rw [heq]
    exact hnative z hz.2
  have hsamp : MapsTo (actualSourceChartTransition (fun _ => c0) e) S
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Data.atlas
        Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i) := by
    intro z hz
    rw [hbackEq (hS hz)]
    exact hsample hz
  have hPhase : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ phase a.source := by
    let pr : X →L[ℝ] ℝ := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m+1) => ℝ) 0).comp
      (ContinuousLinearMap.snd ℝ Ep D)
    have hh := pr.contDiff.contMDiff.comp_contMDiffOn ha
    apply hh.congr
    intro y hy
    exact (hforw y hy).2.symm
  apply actual_secondary_geometry_from_original_core Data hd hs hImm i nu n j T hT e he
    a phase S support W b.source b.open_source hSa hSupportClosed hSupportSource hSourceDomain
    ha (fun z hz => hpair z (by rwa [hat] at hz)) hPhase
    (fun y hy => (hforw y hy).2.symm) hsource
    (fun z hz => hcoord z (by rwa [hat] at hz))
    (by rw [haTarget]; exact hphi) hback
    (by rw [haTarget]; exact hmap) hsamp ell budget c cT Bnative hell hell1 hEll hcT hBnative
    hfinite hbudget hbackBound (by rw [haTarget]; exact hTreserve)
  intro k hk hkj z hz
  rw [hbackJets k z (hS hz)]
  exact hinvjet k hk hkj z hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_secondary_geometry_from_constructed_host
