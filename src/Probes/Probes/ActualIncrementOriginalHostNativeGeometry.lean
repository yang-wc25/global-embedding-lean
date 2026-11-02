import Probes.ActualIncrementOriginalCoreNativeGeometry
import Probes.ActualIncrementHostForwardReserve

/-! A direct consumer of the SAME constructed host refinement. It eliminates
all separately supplied adapted transitions, phase identities, coordinate
membership and forward-chart reserve estimates from the Core producer. -/

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

theorem actual_original_constructed_native_host_geometry
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (j : ℕ)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) e)
    (S : Set X) (hS : S ⊆ b.target)
    (hsource : b.source ⊆ actualOriginalNativeOpen Data i)
    (hsample : MapsTo b.symm S
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Data.atlas
        Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (ell budget c cT Bnative : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (hcT : 0 < cT) (hBnative : 0 < Bnative)
    (hfinite : incrementsOriginalCoreInputProfile Data j ell ≠ ⊤)
    (hbudget : (incrementsOriginalCoreInputProfile Data j ell).toReal ≤ budget)
    (hnative : ∀ z ∈ b.source, ‖fderiv ℝ b z‖ ≤ Bnative)
    (hTreserve : ∀ z ∈ b.target, ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame
        (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
        (e z.1).symm z.2 v‖^2)
    (hinvjet : ∀ k, 1 ≤ k → k ≤ j+2 → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k b.symm z‖ ≤ T k) :
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let Cmap := actualOriginalMapJetCost (m+1) d N j*budget
    let backBound := Bnative
    let Mg := actualAdaptedUniformGeometryCost m N j T c cT backBound Cmap Cmap
    let G := fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2)
    let J := fun z : X => (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2)
    let T0 := fun z : X => incrementsModeTransverseValue (F z.1) (e z.1).symm z.2
    let BR := fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 0 i : V)
    let A := fun z : X => incrementsModeComplexFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2
    let B := fun z : X => incrementsModeComplexFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2
    (∀ z ∈ b.target, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) ((e z.1).symm z.2))) ∧
    (∀ z ∈ b.target,
      let beta := incrementsTransversePairing (F z.1) (hF z.1) ((e z.1).symm z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (e z.1).symm z.2 a.succ)
      (beta.comp beta.adjoint).IsInvertible) ∧
    (ContDiffOn ℝ ∞ G b.target ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k G z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ J b.target ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k J z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ T0 b.target ∧ ∀ k ≤ j, ∀ z ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k T0 z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ BR b.target ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k BR z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ A b.target ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k A z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ B b.target ∧ ∀ k ≤ j, ∀ z ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k B z‖ ≤ Mg) := by
  intro F hF Cmap backBound Mg G J T0 BR A B
  let c0 := Data.atlas.chart i.1
  let psi : Ep × M → ℝ := fun z => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)
  have hdata0 := hdata
  rcases actual_host_slice_geometry_inputs c0 (hd.atlas_smooth.chart_mem i.1) b psi e hdata with
    ⟨hNativeHost,hb,hbi,hcoord,hphi,hback,hmap,hadapt⟩
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hbackEq,hforwardEq,hbackJets,hforwardJets⟩
  have hbase (z : X) (hz : z ∈ b.target) :
      (z.1,(e z.1).symm z.2) ∈ (actualHostAdaptedChart c0 b).source := by
    rw [← hpair z hz]
    exact (actualHostAdaptedChart c0 b).map_target (by rwa [hat])
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
  apply actual_original_core_native_reserved_geometry T hT j Data hd hs hImm i nu e he
    b.target b.source S b.open_target b.open_source hS hsource hcoord hphi hback hmap hsamp
    ell budget c cT Bnative hell hell1 hEll hcT hBnative hfinite hbudget hbackBound hTreserve
  intro k hk hkj z hz
  rw [hbackJets k z (hS hz)]
  exact hinvjet k hk hkj z hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_constructed_native_host_geometry
