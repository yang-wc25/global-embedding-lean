import Probes.ActualIncrementOriginalHostGeometry
import Probes.ActualIncrementOriginalPrimaryFamily

/-! The original-data/Core/constructed-chart producer supplies the SAME
canonical G/J/T0/trueB/A/B fields used by the original actual family. There
is no independent geometry, source, map or coefficient binding hypothesis. -/
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

variable {Β : Type*} [Fintype Β]

theorem actualOriginalPrimaryFamily_geometry_profiles
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (j : ℕ)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M D)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (nu : Fin Data.primaryCount) (beta : Β) (S : Set X)
    (hS : S ⊆ (b nu beta).target)
    (hsource : (b nu beta).source ⊆ actualOriginalNativeOpen Data (host nu beta,i.2))
    (hsample : MapsTo (b nu beta).symm S
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Data.atlas
        Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (host nu beta,i.2)))
    (ell budget c margin Bhost Bnative : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (hmarginPos : 0 < margin) (hBhost : 0 < Bhost) (hBnative : 0 < Bnative)
    (hfinite : incrementsOriginalCoreInputProfile Data j ell ≠ ⊤)
    (hbudget : (incrementsOriginalCoreInputProfile Data j ell).toReal ≤ budget)
    (hhost : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source,
      ‖(tangentSpaceCastModel 𝓙 (Data.atlas.chart (host nu beta) w.2)).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓙 (Data.atlas.chart (host nu beta)) w.2)‖ ≤ Bhost)
    (hnative : ∀ z ∈ (b nu beta).source, ‖fderiv ℝ (b nu beta) z‖ ≤ Bnative)
    (hmargin : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source,
      ∀ (hp : (Data.parameterChart i.2).symm w.1 ∈ Data.parameterOpen),
      let p := (Data.parameterChart i.2).symm w.1
      let xi := incrementsOriginalPhaseCovector Data nu p w.2
      ∀ v : SymmetricSquare xi.ker, margin*‖v‖ ≤
        ‖covectorRestriction (trueSecondFormL (fun y => Data.F (p,y))
          (incrementsOriginal_slice_contMDiff Data hd hs p hp) w.2) xi v‖)
    (hinvjet : ∀ k, 1 ≤ k → k ≤ j+2 → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k (b nu beta).symm z‖ ≤ T k) :
    let g := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let Cmap := actualOriginalMapJetCost (m+1) d N j*budget
    let C := (Bnative*Bhost)^2
    let backBound := Bnative
    let cT := (margin/(C*actualIncrementSortedSymmetricConstant m))^2
    let Mg := actualAdaptedUniformGeometryCost m N j T c cT backBound Cmap Cmap
    let G := fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ (g.inverse nu beta z.1)) z.2)
    let J := fun z : X => (normalSpace (I := 𝓙) (F z.1) ((g.inverse nu beta z.1) z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (g.inverse nu beta z.1) z.2)
    let T0 := fun z : X => incrementsModeTransverseValue (F z.1) (g.inverse nu beta z.1) z.2
    let BR := fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (g.inverse nu beta z.1) z.2 0 i : V)
    let A := fun z : X => incrementsModeComplexFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (g.inverse nu beta z.1) z.2
    let B := fun z : X => incrementsModeComplexFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (g.inverse nu beta z.1) z.2
    (∀ z ∈ (g.chart nu beta).target, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) ((g.inverse nu beta z.1) z.2))) ∧
    (∀ z ∈ (g.chart nu beta).target,
      let beta := incrementsTransversePairing (F z.1) (hF z.1) ((g.inverse nu beta z.1) z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse nu beta z.1) z.2 a.succ)
      (beta.comp beta.adjoint).IsInvertible) ∧
    (ContDiffOn ℝ ∞ G (g.chart nu beta).target ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k G z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ J (g.chart nu beta).target ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k J z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ T0 (g.chart nu beta).target ∧ ∀ k ≤ j, ∀ z ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k T0 z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ BR (g.chart nu beta).target ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k BR z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ A (g.chart nu beta).target ∧ ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k A z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ B (g.chart nu beta).target ∧ ∀ k ≤ j, ∀ z ∈ S, ell^(k+1)*‖iteratedFDeriv ℝ k B z‖ ≤ Mg) := by
  intro g F hF Cmap C backBound cT Mg G J T0 BR A B
  have hcore := actual_original_constructed_host_geometry T hT j Data hd hs hImm
    (host nu beta,i.2) nu (b nu beta) (e nu beta) (hdata nu beta) S hS hsource hsample
    (fun w hw => (hactive nu beta w hw).1) ell budget c margin Bhost Bnative hell hell1
    hEll hmarginPos hBhost hBnative hfinite hbudget hhost hnative hmargin hinvjet
  have htarget : (g.chart nu beta).target = (b nu beta).target := (hdata nu beta).1
  rw [htarget]
  exact hcore

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualOriginalPrimaryFamily_geometry_profiles
