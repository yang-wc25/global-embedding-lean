import Probes.ActualIncrementOriginalCoreChosenGeometry
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

theorem actual_original_constructed_host_geometry
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
    (hprimary : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
      ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain nu)
    (ell budget c eta Bhost Bnative : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (heta : 0 < eta) (hBhost : 0 < Bhost) (hBnative : 0 < Bnative)
    (hfinite : incrementsOriginalCoreInputProfile Data j ell ≠ ⊤)
    (hbudget : (incrementsOriginalCoreInputProfile Data j ell).toReal ≤ budget)
    (hhost : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
      ‖(tangentSpaceCastModel 𝓙 (Data.atlas.chart i.1 w.2)).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓙 (Data.atlas.chart i.1) w.2)‖ ≤ Bhost)
    (hnative : ∀ z ∈ b.source, ‖fderiv ℝ b z‖ ≤ Bnative)
    (hmargin : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
      ∀ (hp : (Data.parameterChart i.2).symm w.1 ∈ Data.parameterOpen),
      let p := (Data.parameterChart i.2).symm w.1
      let xi := incrementsOriginalPhaseCovector Data nu p w.2
      ∀ v : SymmetricSquare xi.ker, eta*‖v‖ ≤
        ‖covectorRestriction (trueSecondFormL (fun y => Data.F (p,y))
          (incrementsOriginal_slice_contMDiff Data hd hs p hp) w.2) xi v‖)
    (hinvjet : ∀ k, 1 ≤ k → k ≤ j+2 → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k b.symm z‖ ≤ T k) :
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let Cmap := actualOriginalMapJetCost (m+1) d N j*budget
    let C := (Bnative*Bhost)^2
    let backBound := Bnative
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
  intro F hF Cmap C backBound cT Mg G J T0 BR A B
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
  apply actual_original_core_chosen_phase_geometry T hT j Data hd hs hImm i nu e he
    b.target b.source S b.open_target b.open_source hS hsource hcoord hphi hback hmap hsamp
    (fun z hz => hprimary _ (hbase z hz)) ell budget c eta C Bnative hell hell1 hEll heta
    (sq_pos_of_pos (mul_pos hBnative hBhost)) hBnative hfinite hbudget hbackBound hadapt
  · intro z hz
    have hv := actual_host_slice_forward_point_norm («Ep» := Ep) (m := m) (M := M)
      c0 (hd.atlas_smooth.chart_mem i.1) b psi e hdata0 hb z.1 ((e z.1).symm z.2)
      (hbase z hz) Bhost Bnative
      (hhost (z.1,(e z.1).symm z.2) (hbase z hz))
      (hnative (z.1,c0 ((e z.1).symm z.2)) (hbase z hz).2)
    exact pow_le_pow_left₀ (norm_nonneg _) hv 2
  · intro z hz
    have hp := actualOriginalNativeOpen_parameter Data i
      (z := actualSourceChartTransition (fun _ => c0) e z) (hsource (hmap hz))
    exact hmargin _ (hbase z hz) hp
  · intro k hk hkj z hz
    rw [hbackJets k z (hS hz)]
    exact hinvjet k hk hkj z hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_constructed_host_geometry
