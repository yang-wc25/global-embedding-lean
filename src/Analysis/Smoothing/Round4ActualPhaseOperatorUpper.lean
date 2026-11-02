import Smoothing.Round4OriginalPairProfileAssembly

/-! The original paperAtlasCj 3 on its actual original sample set supplies
the native joint C3 budget consumed by the SAME template normal factory.
The model comparison is explicit; no adapted reserve or geometry is added. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators NNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance templateNormalRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance templateNormalSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {d m N cParam : ℕ} {P : Type*} [TopologicalSpace P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance templateNormalFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance templateNormalFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance templateNormalHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance templateNormalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance templateNormalTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance templateNormalTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance upperProjectionNormed : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance upperProjectionSpace : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance upperHessianEndNormed : NormedAddCommGroup ((D →L[ℝ] D →L[ℝ] V) →L[ℝ] (D →L[ℝ] D →L[ℝ] V)) := inferInstance
private local instance upperHessianEndSpace : NormedSpace ℝ ((D →L[ℝ] D →L[ℝ] V) →L[ℝ] (D →L[ℝ] D →L[ℝ] V)) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
private local instance templateNormalTangentNormed (x : M) : NormedAddCommGroup (TangentSpace 𝓙 x) := inferInstance
private local instance templateNormalTangentSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓙 x) := inferInstance
private local instance templateNormalTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace 𝓙 x) := inferInstance

theorem round4_actual_phase_operator_norm_from_joint_C2
    (F : Ep → M → V) (host : OpenPartialHomeomorph M D)
    (O : Set X) (hO : IsOpen O)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) O)
    (K2 : ℝ) (hC2 : ∀ z ∈ O, ‖iteratedFDeriv ℝ 2
      (fun y : X => F y.1 (host.symm y.2)) z‖ ≤ K2)
    (z : X) (hz : z ∈ O) :
    ‖round4ActualPhaseOperatorInChart F (fun _ => host) z‖ ≤
      ‖actualHessianLift (E := D) (F := V)‖*K2 := by
  let Q := fderiv ℝ (fderiv ℝ (F z.1 ∘ host.symm)) z.2
  let P := (normalSpace (I := 𝓙) (F z.1) (host.symm z.2)).starProjection
  have hQ : ‖Q‖ ≤ K2 := by
    have h := (spatial_second_jet_le hO hJoint hz 0).trans (hC2 z hz)
    simpa only [Q,Function.comp_def,norm_iteratedFDeriv_zero] using h
  have hP : ‖P‖ ≤ 1 := Submodule.starProjection_norm_le _
  have hPost : ‖actualIncrementPostcomposeHessian D V P‖ ≤ 1 := by
    have hOp : ‖actualIncrementPostcomposeHessian D V‖ ≤ 1 :=
      actualIncrementPostcomposeHessian_norm_le
    exact ((actualIncrementPostcomposeHessian D V).le_opNorm P).trans
      (by simpa using mul_le_mul hOp hP (norm_nonneg P) zero_le_one)
  have hNorm : ‖actualNormalHessianInChart F (fun _ => host) z‖ ≤ K2 := by
    change ‖actualIncrementPostcomposeHessian D V P Q‖ ≤ K2
    exact ((actualIncrementPostcomposeHessian D V P).le_opNorm Q).trans
      ((mul_le_mul_of_nonneg_right hPost (norm_nonneg Q)).trans (by simpa using hQ))
  exact ((actualHessianLift (E := D) (F := V)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left hNorm (norm_nonneg _))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_phase_operator_norm_from_joint_C2
