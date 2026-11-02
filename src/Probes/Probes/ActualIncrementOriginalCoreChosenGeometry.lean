import Probes.ActualIncrementSampleMarginGeometry
import Probes.ActualIncrementOriginalOpenImmersion

/-! The genuine original parameter-open data, original Core, original source
ellipticity and SAME chosen phase margin produce every actual solver geometry
field on the original samples. No full-parameter extension, adapted Hessian
budget, inverse Gram estimate or output coefficient profile is an input. -/

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

variable [RiemannianBundle (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]

private local instance marginTangentNormed (x : M) : NormedAddCommGroup
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x) := inferInstance
private local instance marginTangentSpace (x : M) : NormedSpace ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x) := inferInstance
private local instance marginTangentInner (x : M) : InnerProductSpace ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x) := inferInstance

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

private theorem actual_chosen_margin_congr
    (f g : M → V) (hf : ContMDiff 𝓙 𝓘(ℝ,V) ∞ f) (hg : ContMDiff 𝓙 𝓘(ℝ,V) ∞ g)
    (hfg : f = g) (x : M) (xi : TangentSpace 𝓙 x →L[ℝ] ℝ) (eta : ℝ)
    (hm : ∀ w : SymmetricSquare xi.ker, eta*‖w‖ ≤
      ‖covectorRestriction (trueSecondFormL g hg x) xi w‖) :
    ∀ w : SymmetricSquare xi.ker, eta*‖w‖ ≤
      ‖covectorRestriction (trueSecondFormL f hf x) xi w‖ := by
  cases hfg
  exact hm

theorem actual_original_core_chosen_phase_geometry
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (j : ℕ)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (U W S : Set X) (hU : IsOpen U) (hW : IsOpen W) (hSU : S ⊆ U)
    (hWO : W ⊆ actualOriginalNativeOpen Data i)
    (hcoord : ∀ z ∈ U, z.2 ∈ (e z.1).target ∧
      (e z.1).symm z.2 ∈ (Data.atlas.chart i.1).source)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition (fun _ => Data.atlas.chart i.1) e) U)
    (hback : ContDiffOn ℝ ∞ (actualSourceChartTransition e (fun _ => Data.atlas.chart i.1)) W)
    (hmap : MapsTo (actualSourceChartTransition (fun _ => Data.atlas.chart i.1) e) U W)
    (hsample : MapsTo (actualSourceChartTransition (fun _ => Data.atlas.chart i.1) e) S
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Data.atlas
        Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (hprimary : ∀ z ∈ U,
      ((Data.parameterChart i.2).symm z.1,(e z.1).symm z.2) ∈ Data.primaryDomain nu)
    (ell budget c eta C backBound : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (heta : 0 < eta) (hC : 0 < C) (hbackBoundPos : 0 < backBound)
    (hfinite : incrementsOriginalCoreInputProfile Data j ell ≠ ⊤)
    (hbudget : (incrementsOriginalCoreInputProfile Data j ell).toReal ≤ budget)
    (hbackBound : ∀ z ∈ ((parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i) ∩ W,
      ‖fderiv ℝ (actualSourceChartTransition e (fun _ => Data.atlas.chart i.1)) z‖ ≤ backBound)
    (hadapt : ∀ z ∈ U,
      Data.phase nu ((Data.parameterChart i.2).symm z.1,(e z.1).symm z.2) = z.2 0)
    (hforward : ∀ z ∈ U,
      ‖(tangentSpaceCastModel 𝓙 (e z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓙 (e z.1) ((e z.1).symm z.2))‖^2 ≤ C)
    (hmargin : ∀ z (hz : z ∈ U),
      let p := (Data.parameterChart i.2).symm z.1
      let hp : p ∈ Data.parameterOpen := actualOriginalNativeOpen_parameter Data i
        (z := actualSourceChartTransition (fun _ => Data.atlas.chart i.1) e z) (hWO (hmap hz))
      let xi := incrementsOriginalPhaseCovector Data nu p ((e z.1).symm z.2)
      ∀ w : SymmetricSquare xi.ker, eta*‖w‖ ≤
        ‖covectorRestriction (trueSecondFormL (fun y => Data.F (p,y))
          (incrementsOriginal_slice_contMDiff Data hd hs p hp) ((e z.1).symm z.2)) xi w‖)
    (hphijet : ∀ k, 1 ≤ k → k ≤ j+2 → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k
        (actualSourceChartTransition (fun _ => Data.atlas.chart i.1) e) z‖ ≤ T k) :
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let Cmap := actualOriginalMapJetCost (m+1) d N j*budget
    let cT := (eta/(C*actualIncrementSortedSymmetricConstant m))^2
    let Mg := actualAdaptedUniformGeometryCost m N j T c cT backBound Cmap Cmap
    let G := fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2)
    let J := fun z : X => (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2)
    let T0 := fun z : X => incrementsModeTransverseValue (F z.1) (e z.1).symm z.2
    let BR := fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 0 i : V)
    let A := fun z : X => incrementsModeComplexFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2
    let B := fun z : X => incrementsModeComplexFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2
    (∀ z ∈ U, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) ((e z.1).symm z.2))) ∧
    (∀ z ∈ U,
      let beta := incrementsTransversePairing (F z.1) (hF z.1) ((e z.1).symm z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (e z.1).symm z.2 a.succ)
      (beta.comp beta.adjoint).IsInvertible) ∧
    (ContDiffOn ℝ ∞ G U ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k G z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ J U ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k J z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ T0 U ∧ ∀ k ≤ j, ∀ z ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k T0 z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ BR U ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k BR z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ A U ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k A z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ B U ∧ ∀ k ≤ j, ∀ z ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k B z‖ ≤ Mg) := by
  intro F hF Cmap cT Mg G J T0 BR A B
  let e0 : Ep → OpenPartialHomeomorph M D := fun _ => Data.atlas.chart i.1
  let S0 : Set X := ((parameterTensorModelEquiv (m+1) d) ⁻¹'
    incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
      Data.parameterNormDomain Data.parameterSet i) ∩ W
  let psi : Ep → M → ℝ := fun p x => Data.phase nu ((Data.parameterChart i.2).symm p,x)
  have hS0W : S0 ⊆ W := inter_subset_right
  have hsample0 : MapsTo (actualSourceChartTransition e0 e) S S0 :=
    fun _ hz => ⟨hsample hz,hmap (hSU hz)⟩
  have hF0 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W :=
    (actualOriginalOpenParameterSlice_native_contDiffOn Data hd hs i).mono hWO
  have hinj0 : ∀ z ∈ W, Function.Injective (fderiv ℝ (F z.1 ∘ (e0 z.1).symm) z.2) :=
    fun _ hz => actual_original_open_slice_first_injective Data hd hs hImm i _ (hWO hz)
  have hreserve : ∀ z ∈ S0, ∀ v : D,
      c*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e0 z.1).symm) z.2 v‖^2 :=
    fun _ hz => actual_original_open_slice_coordinate_ellipticity Data hd c hEll i hz.1
  have hCmap : 0 ≤ Cmap := mul_nonneg (actualOriginalMapJetCost_nonneg _ _ _ _)
    (ENNReal.toReal_nonneg.trans hbudget)
  have hprof := actual_original_open_slice_core_profiles Data hd hs j ell hell hell1
    hfinite budget hbudget i
  have hpvalid : ∀ z ∈ U, (Data.parameterChart i.2).symm z.1 ∈ Data.parameterOpen :=
    fun z hz => actualOriginalNativeOpen_parameter Data i
        (z := actualSourceChartTransition (fun _ => Data.atlas.chart i.1) e z) (hWO (hmap hz))
  have hpsi : ∀ z ∈ U, MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2) := by
    intro z hz
    have hO : IsOpen (Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :=
      (hd.primary_open nu).inter (hd.parameter_open.prod isOpen_univ)
    have hj := (hs.phase_joint nu).contMDiffAt
      (hO.mem_nhds ⟨hprimary z hz,hpvalid z hz,mem_univ _⟩)
    exact (hj.comp ((e z.1).symm z.2) (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hm : ∀ z ∈ U,
      let xi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))
      ∀ w : SymmetricSquare xi.ker, eta*‖w‖ ≤
        ‖covectorRestriction (trueSecondFormL (F z.1) (hF z.1) ((e z.1).symm z.2)) xi w‖ := by
    intro z hz
    have heq : F z.1 = fun y => Data.F ((Data.parameterChart i.2).symm z.1,y) :=
      actualOriginalOpenParameterSlice_eq Data i z.1 (hpvalid z hz)
    exact actual_chosen_margin_congr (F z.1)
      (fun y => Data.F ((Data.parameterChart i.2).symm z.1,y)) (hF z.1)
      (incrementsOriginal_slice_contMDiff Data hd hs _ (hpvalid z hz)) heq
      ((e z.1).symm z.2) (incrementsOriginalPhaseCovector Data nu
        ((Data.parameterChart i.2).symm z.1) ((e z.1).symm z.2)) eta (hmargin z hz)
  exact actual_adapted_margin_geometry_on_samples T hT j F hF psi e0 e
    (fun _ => hd.atlas_smooth.chart_mem i.1) he U W S S0 hU hW hSU hS0W
    (fun z hz => actualOriginalNativeMap_source_target Data i (hWO hz).1) hcoord hF0
    hphi hback hmap hsample0 hinj0 ell c eta C backBound Cmap Cmap hell hEll.lower_pos
    heta hC hbackBoundPos hCmap hCmap hreserve hbackBound hpsi hadapt hforward hm
    (fun k hk z hz => hprof.1.2 k hk z hz.1)
    (fun k hk z hz => hprof.2.2 k hk z hz.1) hphijet

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_core_chosen_phase_geometry
