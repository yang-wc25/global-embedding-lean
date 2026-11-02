import GlobalEmbedding.Paper.PeriodicCAlphaDirectionalDerivativeNorm
import GlobalEmbedding.Paper.PeriodicCAlphaPointwiseOperations
import GlobalEmbedding.Paper.PeriodicCAlphaCarrierInjective

/-!
# The actual ambient bounded linear directional derivative

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 399–418.
DAG node: `balanced-holder-directional-derivative-linear`.
-/

namespace GlobalEmbedding.Paper

/-- The actual periodic directional derivative, as a bounded real linear map losing one order.

Proof: the raw derivative is the specified function x↦Df(x)v. Differentiation of sums and
constant scalar multiples gives linearity for the actual pointwise carrier operations.
The proved full original norm bound makes this linear map continuous.
Source: bounded periodic differentiation in the proof of `lem:balanced`. -/
noncomputable def periodicCAlphaDirectionalDerivativeLinear {a N k : ℕ} {α : ℝ}
    (v : EuclideanSpace ℝ (Fin a)) :
    PeriodicCAlphaFunction a N (k + 1) α →L[ℝ] PeriodicCAlphaFunction a N k α :=
  LinearMap.mkContinuous
    ({ toFun := periodicCAlphaDirectionalDerivative v
       map_add' := by
         intro f g
         apply periodicCAlpha_toFun_injective
         funext x
         change fderiv ℝ (f + g).toFun x v =
           (periodicCAlphaDirectionalDerivative v f +
             periodicCAlphaDirectionalDerivative v g).toFun x
         rw [(periodicCAlpha_pointwise_operations a N (k + 1) α).2.1,
           (periodicCAlpha_pointwise_operations a N k α).2.1,
           fderiv_add
             (f.contDiff.differentiable (by simp)).differentiableAt
             (g.contDiff.differentiable (by simp)).differentiableAt]
         rfl
       map_smul' := by
         intro c f
         apply periodicCAlpha_toFun_injective
         funext x
         change fderiv ℝ (c • f).toFun x v = (c • periodicCAlphaDirectionalDerivative v f).toFun x
         rw [(periodicCAlpha_pointwise_operations a N (k + 1) α).2.2,
           (periodicCAlpha_pointwise_operations a N k α).2.2,
           fderiv_const_smul
             (f.contDiff.differentiable (by simp)).differentiableAt]
         rfl } : PeriodicCAlphaFunction a N (k + 1) α →ₗ[ℝ] PeriodicCAlphaFunction a N k α)
    ‖v‖ (periodicCAlphaDirectionalDerivative_norm v)

#print axioms periodicCAlphaDirectionalDerivativeLinear

end GlobalEmbedding.Paper
