import Smoothing.Round4KernelMarginTransport
import Probes.Round4ActualTemplateField
import Probes.ActualIncrementChartMarginReserve

/-! The actual coordinate Hessian operator equals the original intrinsic
true second form after the genuine chart differential on the entire Sym².
The coordinate restricted margin then gives an intrinsic restricted margin
with the explicit squared inverse-chart norm loss. The actual normal-space
inclusion is isometric; no quotient rescaling occurs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Bundle
open scoped ContDiff TensorProduct Topology
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance chartTransportRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance chartTransportSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
private local instance chartTransportTangentNormed (x : M) : NormedAddCommGroup (TangentSpace 𝓙 x) := inferInstance
private local instance chartTransportTangentSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓙 x) := inferInstance
private local instance chartTransportTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace 𝓙 x) := inferInstance

/-- Entire-operator equality on the original quotient, proved by quotient
and tensor extensionality from the actual chart Hessian formula. -/
theorem round4_actual_phase_operator_chart_transport
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (z : X) (hz : z ∈ O) (hcoord : z.2 ∈ (e z.1).target) :
    round4ActualPhaseOperatorInChart F e z =
      ((normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
        (trueSecondFormL (F z.1) (hF z.1) ((e z.1).symm z.2))).comp
          (symmetricSquareMapL
            (actualIncrementChartDerivativeEquiv (e z.1) (he z.1) z.2 hcoord).toContinuousLinearMap) := by
  let A := actualIncrementChartDerivativeEquiv (e z.1) (he z.1) z.2 hcoord
  have hprod (v w : D) :
      round4ActualPhaseOperatorInChart F e z (symmetricSquareProduct D v w) =
        (trueSecondForm (F z.1) (hF z.1) ((e z.1).symm z.2)
          (symmetricSquareProduct (TangentSpace 𝓙 ((e z.1).symm z.2)) (A v) (A w)) : V) := by
    rw [round4_actual_phase_operator_product F e O hO hJoint z hz]
    have he2 : e z.1 ∈ IsManifold.maximalAtlas 𝓙 2 M :=
      IsManifold.maximalAtlas_subset_of_le (by simp) (he z.1)
    have hcv (v : D) : mfderiv 𝓙 𝓙 (e z.1) ((e z.1).symm z.2) (A v) = v :=
      A.symm_apply_apply v
    rw [← trueSecondForm_chart (F z.1) (hF z.1) ((e z.1).symm z.2)
      (e z.1) he2 ((e z.1).map_target hcoord)]
    change (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection
        (fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2 v w) =
      (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).starProjection
        (fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) ((e z.1) ((e z.1).symm z.2))
          (mfderiv 𝓙 𝓙 (e z.1) ((e z.1).symm z.2) (A v))
          (mfderiv 𝓙 𝓙 (e z.1) ((e z.1).symm z.2) (A w)))
    rw [hcv, hcv, (e z.1).right_inv hcoord]
  let Q := ((normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
      (trueSecondFormL (F z.1) (hF z.1) ((e z.1).symm z.2))).comp
        (symmetricSquareMapL A.toContinuousLinearMap)
  change round4ActualPhaseOperatorInChart F e z = Q
  apply ContinuousLinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ t =>
    induction t using TensorProduct.inductionOn with
    | tmul v w =>
      change round4ActualPhaseOperatorInChart F e z (symmetricSquareProduct D v w) = _
      exact hprod v w
    | add a b ha hb =>
      change round4ActualPhaseOperatorInChart F e z (symmetricSquareQuotient D (a+b)) =
        Q (symmetricSquareQuotient D (a+b))
      simp only [map_add]
      exact congrArg₂ (·+·) ha hb

/-- This consumes the actual coordinate operator produced by the uniform
template family, and returns the margin of the actual intrinsic true form. -/
theorem round4_actual_coordinate_margin_to_intrinsic
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (z : X) (hz : z ∈ O) (hcoord : z.2 ∈ (e z.1).target)
    (xi : D →L[ℝ] ℝ) (eta C : ℝ) (heta : 0 ≤ eta) (hC : 0 < C)
    (hInverse : ‖(actualIncrementChartDerivativeEquiv (e z.1) (he z.1) z.2 hcoord).toContinuousLinearMap‖^2 ≤ C)
    (hmargin : ∀ w : SymmetricSquare xi.ker, eta*‖w‖ ≤
      ‖covectorRestriction (round4ActualPhaseOperatorInChart F e z) xi w‖) :
    let xiT := xi.comp (mfderiv 𝓙 𝓙 (e z.1) ((e z.1).symm z.2))
    ∀ w : SymmetricSquare xiT.ker, (eta/C)*‖w‖ ≤
      ‖covectorRestriction (trueSecondFormL (F z.1) (hF z.1) ((e z.1).symm z.2)) xiT w‖ := by
  let A := actualIncrementChartDerivativeEquiv (e z.1) (he z.1) z.2 hcoord
  let T := (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
    (trueSecondFormL (F z.1) (hF z.1) ((e z.1).symm z.2))
  have hBT := round4_actual_phase_operator_chart_transport F hF e he O hO hJoint z hz hcoord
  intro xiT w
  exact round4_covector_margin_coordinate_to_intrinsic A xi
    (round4ActualPhaseOperatorInChart F e z) T hBT eta C heta hC hInverse hmargin w

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_phase_operator_chart_transport
#print axioms GlobalEmbedding.Continuation.round4_actual_coordinate_margin_to_intrinsic
