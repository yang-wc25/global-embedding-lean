import Repair.EndpointTemplateData
import Probes.Round4TemplateCoefficientJets
import Smoothing.WeightedActualGram

/-! The original linear-functional coordinate field is a fixed template
coefficient applied to the literal symmetric coordinate tensor pulled through
the actual host differential. Its dependence on the receiving chart is the
quadratic Jacobian expression, not an independently supplied coefficient field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle
open scoped BigOperators ContDiff
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "In" => 𝓘(ℝ,En)

theorem repair_original_symmetric_coordinate_tensor_apply
    (Data : IncrementsOriginalNativeData n d N M P)
    (i : Fin Data.atlas.count) (x : M) (r s : Fin n)
    (v w : TangentSpace In x) :
    (incrementsOriginalSymmetricCoordinateTensor Data i x r s).val v w =
      (1/2 : ℝ) *
        (incrementsOriginalSourceChartDifferential Data i x v r *
          incrementsOriginalSourceChartDifferential Data i x w s +
         incrementsOriginalSourceChartDifferential Data i x v s *
          incrementsOriginalSourceChartDifferential Data i x w r) := by
  classical
  simp only [incrementsOriginalSymmetricCoordinateTensor, LinearMap.BilinForm.comp_apply,
    Matrix.toBilin'_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul]
  simp [Matrix.single, ite_and, mul_add, add_mul, mul_ite, ite_mul,
    Finset.sum_add_distrib, eq_comm]
  ring

private local instance repairJacTensorNormed :
    NormedAddCommGroup (En →L[ℝ] En →L[ℝ] ℝ) := inferInstance
private local instance repairJacTensorSpace :
    NormedSpace ℝ (En →L[ℝ] En →L[ℝ] ℝ) := inferInstance

def repairSymmetricJacobianTensor (R : En →L[ℝ] En) (r s : Fin n) :
    En →L[ℝ] En →L[ℝ] ℝ :=
  (1/2 : ℝ) •
    (((EuclideanSpace.proj r).comp R).smulRight ((EuclideanSpace.proj s).comp R) +
     ((EuclideanSpace.proj s).comp R).smulRight ((EuclideanSpace.proj r).comp R))

@[simp] theorem repairSymmetricJacobianTensor_apply (R : En →L[ℝ] En)
    (r s : Fin n) (v w : En) :
    repairSymmetricJacobianTensor R r s v w =
      (1/2 : ℝ) * ((R v) r * (R w) s + (R v) s * (R w) r) := rfl

variable {m : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,D)

theorem repair_host_template_actual_coordinate_tensor
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (own : OpenPartialHomeomorph M D)
    (hown : own ∈ IsManifold.maximalAtlas IT ∞ M)
    (template : ActualGoodDictionaryTemplate D V)
    (a : EdgePair (Module.finrank ℝ D+1))
    (i : Fin Data.atlas.count) (x : M) (hx : x ∈ own.source) (r s : Fin (m+1)) :
    repairHostTemplateArgument own hown template a x
      (incrementsOriginalSymmetricCoordinateTensor Data i x r s).val =
    template.coefficients (repairSymmetricJacobianTensor
      ((EuclideanSpace.equiv (Fin (m+1)) ℝ).symm.toContinuousLinearMap.comp
        ((incrementsOriginalSourceChartDifferential Data i x).comp
          (repairHostInverseDifferential own hown x hx).toContinuousLinearMap)) r s) a := by
  unfold repairHostTemplateArgument repairNativeTemplateArgument repairNativeTemplateCoefficients
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, ContinuousLinearMap.coe_coe]
  apply congrArg (fun Q : D →L[ℝ] D →L[ℝ] ℝ => template.coefficients Q a)
  ext v w
  rw [repairNativeTensorPullback_apply, repairHostTensorInverse_on_source own hown x hx,
    repair_original_symmetric_coordinate_tensor_apply, repairSymmetricJacobianTensor_apply]
  rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_host_template_actual_coordinate_tensor

