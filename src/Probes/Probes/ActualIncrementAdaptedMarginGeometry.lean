import Probes.ActualIncrementAdaptedGeometry
import Probes.ActualIncrementAdaptedPhaseReserve
import Probes.ActualIncrementReserveAdmissibility

/-! The margin of the SAME chosen phase and its actual chart identity supply
both original mode admissibility conditions and every geometric solver profile.
No transverse reserve, inverse Gram or desired adapted coefficient budget is
an assumption. The ordinary connection retains its required shift one. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Bundle
open scoped ContDiff Topology BigOperators TensorProduct
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

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

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

theorem actual_adapted_uniform_geometry_from_chosen_margin
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (psi : Ep → M → ℝ)
    (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (he0 : ∀ p, e0 p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (he1 : ∀ p, e1 p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (U W : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hcoord0 : ∀ z ∈ W, z.2 ∈ (e0 z.1).target)
    (hcoord : ∀ z ∈ U, z.2 ∈ (e1 z.1).target ∧ (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (hF0 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hback : ContDiffOn ℝ ∞ (actualSourceChartTransition e1 e0) W)
    (hmap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (ell c eta C backBound MA MH : ℝ) (hell : 0 < ell)
    (hc : 0 < c) (heta : 0 < eta) (hC : 0 < C) (hbackBoundPos : 0 < backBound)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ W, ∀ v : D,
      c*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e0 z.1).symm) z.2 v‖^2)
    (hbackBound : ∀ z ∈ W, ‖fderiv ℝ (actualSourceChartTransition e1 e0) z‖ ≤ backBound)
    (hpsi : ∀ z ∈ U, MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e1 z.1).symm z.2))
    (hadapt : ∀ z ∈ U, psi z.1 ((e1 z.1).symm z.2) = z.2 0)
    (hforward : ∀ z ∈ U,
      ‖(tangentSpaceCastModel 𝓙 (e1 z.1 ((e1 z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓙 (e1 z.1) ((e1 z.1).symm z.2))‖^2 ≤ C)
    (hmargin : ∀ z ∈ U,
      let xi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.1 ((e1 z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e1 z.1).symm z.2))
      ∀ w : SymmetricSquare xi.ker, eta*‖w‖ ≤
        ‖covectorRestriction (trueSecondFormL (F z.1) (hF z.1) ((e1 z.1).symm z.2)) xi w‖)
    (hAj : ∀ k ≤ j+1, ∀ z ∈ W, ell^k*‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e0 y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ z ∈ W, ell^k*‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e0 y.1).symm)) y.2) z‖ ≤ MH)
    (hphijet : ∀ k, 1 ≤ k → k ≤ j+2 → ∀ z ∈ U,
      ell^(k-1)*‖iteratedFDeriv ℝ k (actualSourceChartTransition e0 e1) z‖ ≤ T k) :
    let cT := (eta/(C*actualIncrementSortedSymmetricConstant m))^2
    let Mg := actualAdaptedUniformGeometryCost m N j T c cT backBound MA MH
    let G := fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2)
    let J := fun z : X => (normalSpace (I := 𝓙) (F z.1) ((e1 z.1).symm z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (I := 𝓙) (F z.1) (hF z.1) (e1 z.1).symm z.2)
    let T0 := fun z : X => incrementsModeTransverseValue (F z.1) (e1 z.1).symm z.2
    let BR := fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e1 z.1).symm z.2 0 i : V)
    let A := fun z : X => incrementsModeComplexFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (e1 z.1).symm z.2
    let B := fun z : X => incrementsModeComplexFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (e1 z.1).symm z.2
    (∀ z ∈ U, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) ((e1 z.1).symm z.2))) ∧
    (∀ z ∈ U,
      let beta := incrementsTransversePairing (F z.1) (hF z.1) ((e1 z.1).symm z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (e1 z.1).symm z.2 a.succ)
      (beta.comp beta.adjoint).IsInvertible) ∧
    (ContDiffOn ℝ ∞ G U ∧ ∀ k ≤ j, ∀ z ∈ U, ell^k*‖iteratedFDeriv ℝ k G z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ J U ∧ ∀ k ≤ j, ∀ z ∈ U, ell^k*‖iteratedFDeriv ℝ k J z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ T0 U ∧ ∀ k ≤ j, ∀ z ∈ U, ell^(k+1)*‖iteratedFDeriv ℝ k T0 z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ BR U ∧ ∀ k ≤ j, ∀ z ∈ U, ell^k*‖iteratedFDeriv ℝ k BR z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ A U ∧ ∀ k ≤ j, ∀ z ∈ U, ell^k*‖iteratedFDeriv ℝ k A z‖ ≤ Mg) ∧
    (ContDiffOn ℝ ∞ B U ∧ ∀ k ≤ j, ∀ z ∈ U, ell^(k+1)*‖iteratedFDeriv ℝ k B z‖ ≤ Mg) := by
  intro cT Mg G J T0 BR A B
  have hcT : 0 < cT := sq_pos_of_pos
    (div_pos heta (mul_pos hC (actualIncrementSortedSymmetricConstant_pos m)))
  have hTres : ∀ z ∈ U, ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (I := 𝓙) (F z.1) (hF z.1) (e1 z.1).symm z.2 v‖^2 := by
    intro z hz v
    let O : Set D := (fun x : D => (z.1,x)) ⁻¹' U
    have hO : IsOpen O := hU.preimage (continuous_const.prodMk continuous_id)
    exact actual_increment_adapted_phase_frame_reserve (F z.1) (hF z.1) (psi z.1)
      (e1 z.1) (he1 z.1) O hO (fun x hx => (hcoord (z.1,x) hx).1) z.2 hz
      (hpsi z hz) (fun x hx => hadapt (z.1,x) hx) eta C heta.le hC (hforward z hz) (hmargin z hz) v
  have hfirst := actual_adapted_first_frame_reserve_from_original F e0 e1 U W hU hW hF0
    hphi hback hmap hcoord c backBound hc hbackBoundPos hreserve hbackBound
  refine ⟨?_,?_,?_⟩
  · intro z hz
    exact actual_increment_manifold_injective_of_first_reserve (F z.1) (hF z.1)
      (e1 z.1) (he1 z.1) z.2 (hcoord z hz).1 (c/backBound^2)
      (div_pos hc (sq_pos_of_pos hbackBoundPos)) (hfirst z hz)
  · intro z hz
    exact actual_increment_transverse_gram_of_reserve (F z.1) (hF z.1)
      (e1 z.1).symm z.2 cT hcT (hTres z hz)
  · exact actual_adapted_uniform_geometry_from_original_jets T hT j F hF e0 e1 he0 he1
      U W hU hW hcoord0 hcoord hF0 hphi hback hmap ell c cT backBound MA MH hell hc hcT
      hbackBoundPos hMA hMH hreserve hbackBound hTres hAj hHj hphijet

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_adapted_uniform_geometry_from_chosen_margin
