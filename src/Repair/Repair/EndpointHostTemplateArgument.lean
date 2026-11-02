import Repair.EndpointTemplateCoefficients
import Repair.ReferenceSlicePhases

/-! The original template functional uses the actual inverse differential of
its host chart at the actual source point. Its outside extension is zero;
all identities are on the original chart source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle
open scoped BigOperators ContDiff
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "I" => 𝓘(ℝ,D)

def repairHostInverseDifferential
    (host : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas I ∞ M)
    (x : M) (hx : x ∈ host.source) : D ≃L[ℝ] TangentSpace I x :=
  ((actual_increment_maximal_chart_mdifferentiable host hhost).mfderiv hx).symm

def repairHostTensorInverse
    (host : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas I ∞ M)
    (x : M) : D →ₗ[ℝ] TangentSpace I x := by
  classical
  exact if hx : x ∈ host.source then
    (repairHostInverseDifferential host hhost x hx).toLinearMap else 0

@[simp] theorem repairHostTensorInverse_on_source
    (host : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas I ∞ M)
    (x : M) (hx : x ∈ host.source) :
    repairHostTensorInverse host hhost x =
      (repairHostInverseDifferential host hhost x hx).toLinearMap := by
  simp only [repairHostTensorInverse, dite_eq_left hx]

def repairHostTemplateArgument
    (host : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas I ∞ M)
    (template : ActualGoodDictionaryTemplate D V)
    (a : EdgePair (Module.finrank ℝ D+1)) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) →ₗ[ℝ] ℝ :=
  repairNativeTemplateArgument template (repairHostTensorInverse host hhost x) a

theorem repair_host_template_linear_reconstruction
    (host : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas I ∞ M)
    (template : ActualGoodDictionaryTemplate D V)
    (x : M) (hx : x ∈ host.source)
    (A : LinearMap.BilinForm ℝ (TangentSpace I x)) (hA : A.IsSymm) :
    A = ∑ a, repairHostTemplateArgument host hhost template a x A •
      LinearMap.BilinForm.comp (LinearMap.mul ℝ ℝ)
        (round4HostPhaseCovector host (template.covectors a) x).toLinearMap
        (round4HostPhaseCovector host (template.covectors a) x).toLinearMap := by
  have hphase (a : EdgePair (Module.finrank ℝ D+1)) :
      round4HostPhaseCovector host (template.covectors a) x =
        (template.covectors a).comp
          (repairHostInverseDifferential host hhost x hx).symm.toContinuousLinearMap := by
    exact repair_reference_source_linear_covector host hhost _ x hx
  have hrec := repair_native_template_linear_reconstruction template
    (repairHostInverseDifferential host hhost x hx).toLinearEquiv A hA
  calc
    A = ∑ a, repairHostTemplateArgument host hhost template a x A •
      LinearMap.BilinForm.comp (LinearMap.mul ℝ ℝ)
        ((template.covectors a).toLinearMap.comp
          (repairHostInverseDifferential host hhost x hx).symm.toLinearMap)
        ((template.covectors a).toLinearMap.comp
          (repairHostInverseDifferential host hhost x hx).symm.toLinearMap) := by
      simpa only [repairHostTemplateArgument, repairHostTensorInverse_on_source host hhost x hx,
        ← ContinuousLinearEquiv.toLinearEquiv_symm]
        using hrec
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hphase a]
      rfl

theorem repair_host_template_reserve
    (host : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas I ∞ M)
    (template : ActualGoodDictionaryTemplate D V)
    (x : M) (A : LinearMap.BilinForm ℝ (TangentSpace I x))
    (hA : repairNativeTensorPullback (repairHostTensorInverse host hhost x) A ∈ template.tensorDomain)
    (a : EdgePair (Module.finrank ℝ D+1)) :
    template.coefficientReserve ≤ repairHostTemplateArgument host hhost template a x A :=
  repair_native_template_reference_reserve template _ A hA a

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_host_template_linear_reconstruction

