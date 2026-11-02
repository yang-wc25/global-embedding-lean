import Smoothing.Round4GoodCovectorTransport
import Smoothing.Round4ActualPhaseMarginTransport
import GlobalEmbedding.Paper.GoodCovectorNormedCriterion

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

/-- The actual native good covector gives the original canonical
GoodCovector. This is algebraic covariance; no quantitative intrinsic norm
bound or uniform Riemannian conditioning is asserted or needed. -/
theorem round4_actual_coordinate_good_to_intrinsic
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (z : X) (hz : z ∈ O) (hcoord : z.2 ∈ (e z.1).target)
    (xi : D →L[ℝ] ℝ)
    (hGood : LinearSecondFormGoodCovector (round4ActualPhaseOperatorInChart F e z).toLinearMap xi.toLinearMap) :
    GoodCovector (F z.1) (hF z.1) ((e z.1).symm z.2)
      (xi.comp (mfderiv 𝓙 𝓙 (e z.1) ((e z.1).symm z.2))) := by
  let A := actualIncrementChartDerivativeEquiv (e z.1) (he z.1) z.2 hcoord
  let T := (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL.comp
    (trueSecondFormL (F z.1) (hF z.1) ((e z.1).symm z.2))
  have hBT := round4_actual_phase_operator_chart_transport F hF e he O hO hJoint z hz hcoord
  have hg := round4_good_covector_coordinate_to_intrinsic A xi
    (round4ActualPhaseOperatorInChart F e z) T hBT hGood
  obtain ⟨hne,hinj⟩ := (linearSecondFormGoodCovector_iff_native_restriction T _).mp hg
  apply (good_covector_iff_normed (F z.1) (hF z.1) ((e z.1).symm z.2) _).mpr
  refine ⟨hne,?_⟩
  intro u v huv
  apply hinj
  exact congrArg (normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2)).subtypeL huv

theorem round4_actual_host_linear_phase_covector
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (xi : D →L[ℝ] ℝ) (x : D) (hx : x ∈ host.target) :
    (tangentSpaceCastModel 𝓘(ℝ,ℝ) (xi (host (host.symm x)))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun y => xi (host y)) (host.symm x)) =
      xi.comp (mfderiv 𝓙 𝓙 host (host.symm x)) := by
  have hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (fun y => xi (host y)) (host.symm x) :=
    xi.differentiableAt.mdifferentiableAt.comp _
      ((actual_increment_maximal_chart_mdifferentiable host hhost).mdifferentiableAt (host.map_target hx))
  exact round4_actual_linear_phase_covector_eq_chart (fun y => xi (host y)) host hhost
    host.target host.open_target Subset.rfl x hx hpsi xi
    (fun y hy => congrArg xi (host.right_inv hy))

theorem round4_actual_host_linear_phase_good
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) O)
    (z : X) (hz : z ∈ O) (hcoord : z.2 ∈ host.target)
    (xi : D →L[ℝ] ℝ)
    (hGood : LinearSecondFormGoodCovector
      (round4ActualPhaseOperatorInChart F (fun _ => host) z).toLinearMap xi.toLinearMap) :
    GoodCovector (F z.1) (hF z.1) (host.symm z.2)
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (xi (host (host.symm z.2)))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun y => xi (host y)) (host.symm z.2))) := by
  rw [round4_actual_host_linear_phase_covector host hhost xi z.2 hcoord]
  exact round4_actual_coordinate_good_to_intrinsic F hF (fun _ => host) (fun _ => hhost)
    O hO hJoint z hz hcoord xi hGood

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_coordinate_good_to_intrinsic
#print axioms GlobalEmbedding.Continuation.round4_actual_host_linear_phase_good
