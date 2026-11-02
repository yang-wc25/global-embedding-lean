import GlobalEmbedding.Paper.PeriodicCAlphaSpace
import GlobalEmbedding.Paper.PeriodicCAlphaGlobalJetBound
import GlobalEmbedding.Paper.PeriodicCAlphaPointwiseOperations
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The bounded continuous jet maps of actual periodic Hölder functions

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-bounded-jet-map`.
-/

open scoped BoundedContinuousFunction

namespace GlobalEmbedding.Paper

/-- The j-th derivative of an actual periodic Hölder element, bundled as a bounded continuous
function of its Euclidean lift, is a continuous linear map of the original element.

Global boundedness uses the actual Hölder formula, with bound constant one. Linearity is
pointwise derivative linearity for C^k functions. No completeness of the Hölder carrier is
assumed. Source: `lem:balanced`, periodic Hölder completeness expansion. -/
noncomputable def periodicCAlphaJetMap {a N k : ℕ} {α : ℝ} (j : ℕ) (hj : j ≤ k) :
    PeriodicCAlphaFunction a N k α →L[ℝ]
      (EuclideanSpace ℝ (Fin a) →ᵇ
        ((EuclideanSpace ℝ (Fin a)) [×j]→L[ℝ] EuclideanSpace ℝ (Fin N))) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ BoundedContinuousFunction.ofNormedAddCommGroup
        (iteratedFDeriv ℝ j f.toFun)
        (ContDiff.continuous_iteratedFDeriv (by exact_mod_cast hj) f.contDiff)
        (periodicCAlphaNorm f) (periodicCAlpha_global_jet_bound f j hj)
      map_add' := by
        intro f g
        apply BoundedContinuousFunction.ext
        intro x
        change iteratedFDeriv ℝ j (f + g).toFun x =
          iteratedFDeriv ℝ j f.toFun x + iteratedFDeriv ℝ j g.toFun x
        rw [(periodicCAlpha_pointwise_operations a N k α).2.1 f g]
        exact iteratedFDeriv_add_apply
          (f.contDiff.of_le (by exact_mod_cast hj)).contDiffAt
          (g.contDiff.of_le (by exact_mod_cast hj)).contDiffAt
      map_smul' := by
        intro c f
        apply BoundedContinuousFunction.ext
        intro x
        change iteratedFDeriv ℝ j (c • f).toFun x = c • iteratedFDeriv ℝ j f.toFun x
        rw [(periodicCAlpha_pointwise_operations a N k α).2.2 c f]
        exact iteratedFDeriv_const_smul_apply
          (f.contDiff.of_le (by exact_mod_cast hj)).contDiffAt }
    1 (by
      intro f
      simp only [one_mul]
      exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
        (periodicCAlphaNorm_nonnegative f) (periodicCAlpha_global_jet_bound f j hj))

#print axioms periodicCAlphaJetMap

end GlobalEmbedding.Paper
