import Smoothing.Round4OriginalTensorReconstruction
import GlobalEmbedding.Offline.CompactGoodDictionaryTemplates
import Repair.EndpointLocalDictionaryAssembly

/-!
# Actual template coefficients on the original native tensor fiber

The functional is the chosen template's original continuous linear coefficient
map applied to the literal inverse-chart pullback. It is defined for every
native tensor argument. Its reconstruction proof uses the template's linear
right inverse, so no positivity or desired reconstruction is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set
open scoped BigOperators
namespace GlobalEmbedding.Continuation

variable {n : ℕ} {T V : Type*} [AddCommGroup T] [Module ℝ T]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
local notation "D" => EuclideanSpace ℝ (Fin n)

private local instance repairTemplateBilinGroup :
    AddCommGroup (LinearMap.BilinForm ℝ T) := LinearMap.addCommGroup

/-- Evaluation on the actual inverse-chart images of the standard basis. -/
def repairNativeTensorEvaluations (J : D →ₗ[ℝ] T) :
    LinearMap.BilinForm ℝ T →ₗ[ℝ] (Fin (n*n) → ℝ) where
  toFun A a := A (J (EuclideanSpace.single (finProdFinEquiv.symm a).1 1))
    (J (EuclideanSpace.single (finProdFinEquiv.symm a).2 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def repairNativeTensorPullback (J : D →ₗ[ℝ] T) :
    LinearMap.BilinForm ℝ T →ₗ[ℝ] (D →L[ℝ] D →L[ℝ] ℝ) :=
  (round4NativeTensorFromCoordinates n).toLinearMap.comp
    (repairNativeTensorEvaluations J)

@[simp] theorem repairNativeTensorPullback_forget (J : D →ₗ[ℝ] T)
    (A : LinearMap.BilinForm ℝ T) :
    continuousBilinearForget (repairNativeTensorPullback J A) = A.comp J J := by
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  intro r
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  intro s
  simp only [repairNativeTensorPullback, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, continuousBilinearForget_apply,
    round4NativeTensorFromCoordinates_basis]
  change A (J (EuclideanSpace.single (finProdFinEquiv.symm (finProdFinEquiv (r,s))).1 1))
    (J (EuclideanSpace.single (finProdFinEquiv.symm (finProdFinEquiv (r,s))).2 1)) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem repairNativeTensorPullback_apply (J : D →ₗ[ℝ] T)
    (A : LinearMap.BilinForm ℝ T) (v w : D) :
    repairNativeTensorPullback J A v w = A (J v) (J w) :=
  congrArg (fun B : LinearMap.BilinForm ℝ D => B v w)
    (repairNativeTensorPullback_forget J A)

def repairNativeTemplateCoefficients (template : ActualGoodDictionaryTemplate D V)
    (J : D →ₗ[ℝ] T) :
    LinearMap.BilinForm ℝ T →ₗ[ℝ]
      (EdgePair (Module.finrank ℝ D + 1) → ℝ) :=
  template.coefficients.toLinearMap.comp (repairNativeTensorPullback J)

def repairNativeTemplateArgument (template : ActualGoodDictionaryTemplate D V)
    (J : D →ₗ[ℝ] T) (a : EdgePair (Module.finrank ℝ D + 1)) :
    LinearMap.BilinForm ℝ T →ₗ[ℝ] ℝ :=
  (LinearMap.proj a).comp (repairNativeTemplateCoefficients template J)

/-- The same coefficient functional reconstructs every symmetric native
tensor, before restricting to the positive neighborhood. -/
theorem repair_native_template_linear_reconstruction
    (template : ActualGoodDictionaryTemplate D V) (J : D ≃ₗ[ℝ] T)
    (A : LinearMap.BilinForm ℝ T) (hA : A.IsSymm) :
    A = ∑ a, repairNativeTemplateArgument template J.toLinearMap a A •
      LinearMap.BilinForm.comp (LinearMap.mul ℝ ℝ)
        ((template.covectors a).toLinearMap.comp J.symm.toLinearMap)
        ((template.covectors a).toLinearMap.comp J.symm.toLinearMap) := by
  have hSym : ∀ v w, repairNativeTensorPullback J.toLinearMap A v w =
      repairNativeTensorPullback J.toLinearMap A w v := by
    intro v w
    simp only [repairNativeTensorPullback_apply]
    exact hA.eq _ _
  have hrec := template.coefficient_right_inverse
    (repairNativeTensorPullback J.toLinearMap A) hSym
  ext u v
  have h := congrArg (fun B : D →L[ℝ] D →L[ℝ] ℝ =>
    B (J.symm u) (J.symm v)) hrec
  simpa [continuousRankOneReconstruct_apply, repairNativeTemplateArgument,
    repairNativeTemplateCoefficients, LinearMap.comp_apply,
    repairNativeTensorPullback_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, mul_assoc] using h.symm

theorem repair_native_template_reference_reserve
    (template : ActualGoodDictionaryTemplate D V) (J : D →ₗ[ℝ] T)
    (A : LinearMap.BilinForm ℝ T)
    (hA : repairNativeTensorPullback J A ∈ template.tensorDomain)
    (a : EdgePair (Module.finrank ℝ D + 1)) :
    template.coefficientReserve ≤ repairNativeTemplateArgument template J a A :=
  template.coefficient_control _ hA a

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_native_template_linear_reconstruction
#print axioms GlobalEmbedding.Continuation.repair_native_template_reference_reserve

