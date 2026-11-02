import Smoothing.Round4NativeSpatialKernel
import Probes.Round4ActualTemplateField
import Probes.ActualIncrementSampleNormalTransfer

/-! Native Euclidean restricted margins give the original sorted transverse
frame reserve. The genuine normal Hessian transition retains both Jacobian
factors; no comparison with a Riemannian tangent-fibre norm is required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Bundle
open scoped ContDiff Topology TensorProduct BigOperators
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance nativeFrameRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance nativeFrameSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "D0" => EuclideanSpace ℝ (Fin m)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem round4_actual_native_frame_eq_restriction
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (he1 : ∀ p, e1 p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (W : Set X) (hW : IsOpen W)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (y : X) (hy : y ∈ W) (z : X) (hz : z.2 ∈ (e1 z.1).target)
    (A : D ≃L[ℝ] D)
    (hQ : actualNormalHessianInChart F e1 z =
      (actualNormalHessianInChart F e0 y).bilinearComp A.toContinuousLinearMap A.toContinuousLinearMap)
    (t : Tdata) :
    incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e1 z.1).symm z.2 t =
      covectorRestriction (round4ActualPhaseOperatorInChart F e0 y)
        (actualIncrementCoordinateCovector A)
        (symmetricSquareMap (actualIncrementCoordinateKernelEquiv A).toContinuousLinearMap
          (actualIncrementSortedSymmetricLinear m t)) := by
  rw [← symmetricSquareMapL_apply, actualIncrementSortedSymmetricLinear_apply]
  simp only [map_sum, map_smul]
  unfold incrementsModeAmbientTransverseFrame
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  unfold covectorRestriction
  simp only [ContinuousLinearMap.comp_apply, symmetricSquareMapL_product]
  change (incrementsModeSecondForm (F z.1) (hF z.1) (e1 z.1).symm z.2
      q.val.1.succ q.val.2.succ : V) =
    round4ActualPhaseOperatorInChart F e0 y (symmetricSquareProduct D
      ((actualIncrementCoordinateKernelEquiv A (EuclideanSpace.single q.val.1 1)) : D)
      ((actualIncrementCoordinateKernelEquiv A (EuclideanSpace.single q.val.2 1)) : D))
  rw [actualIncrementCoordinateKernelEquiv_single, actualIncrementCoordinateKernelEquiv_single,
    round4_actual_phase_operator_product F e0 W hW hJoint y hy]
  rw [actual_increment_secondForm_chart (F z.1) (hF z.1) (e1 z.1) (he1 z.1)
    z.2 hz q.val.1.succ q.val.2.succ]
  exact congrArg (fun Q : D →L[ℝ] D →L[ℝ] V =>
    Q (EuclideanSpace.single q.val.1.succ 1) (EuclideanSpace.single q.val.2.succ 1)) hQ

theorem round4_actual_native_frame_reserve
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (he1 : ∀ p, e1 p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (W : Set X) (hW : IsOpen W)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (y : X) (hy : y ∈ W) (z : X) (hz : z.2 ∈ (e1 z.1).target)
    (A : D ≃L[ℝ] D)
    (hQ : actualNormalHessianInChart F e1 z =
      (actualNormalHessianInChart F e0 y).bilinearComp A.toContinuousLinearMap A.toContinuousLinearMap)
    (xi : D →L[ℝ] ℝ) (hxi : actualIncrementCoordinateCovector A = xi)
    (eta C : ℝ) (heta : 0 ≤ eta) (hC : 0 < C)
    (hInverse : ‖A.symm.toContinuousLinearMap‖^2 ≤ C)
    (hmargin : ∀ w : SymmetricSquare xi.ker, eta*‖w‖ ≤
      ‖covectorRestriction (round4ActualPhaseOperatorInChart F e0 y) xi w‖)
    (t : Tdata) :
    (eta/(C*actualIncrementSortedSymmetricConstant m))^2*‖t‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e1 z.1).symm z.2 t‖^2 := by
  subst xi
  rw [round4_actual_native_frame_eq_restriction F hF e0 e1 he1 W hW hJoint y hy z hz A hQ]
  apply actual_increment_sorted_transport_reserve m (actualIncrementCoordinateKernelEquiv A)
    (covectorRestriction (round4ActualPhaseOperatorInChart F e0 y) (actualIncrementCoordinateCovector A))
    eta C heta hC _ hmargin t
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr
    (actualIncrementCoordinateKernelEquiv_inverse_norm A)).trans hInverse

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_native_frame_eq_restriction
#print axioms GlobalEmbedding.Continuation.round4_actual_native_frame_reserve
