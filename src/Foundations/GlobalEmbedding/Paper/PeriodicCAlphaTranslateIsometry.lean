import GlobalEmbedding.Paper.PeriodicCAlphaTranslateNorm
import GlobalEmbedding.Paper.PeriodicCAlphaPointwiseOperations
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# The actual ambient Hölder translation linear isometry

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-ambient-translation-isometry`.
-/

namespace GlobalEmbedding.Paper

/-- The actual translation f(x)↦f(x+h), as a real linear isometry of the ambient Hölder space.

Linearity follows from the actual pointwise operations; norm preservation is the exact
periodic Hölder norm identity. Source: translation in the proof of `lem:balanced`. -/
noncomputable def periodicCAlphaTranslateIsometry {a N k : ℕ} {α : ℝ}
    (h : EuclideanSpace ℝ (Fin a)) :
    PeriodicCAlphaFunction a N k α →ₗᵢ[ℝ] PeriodicCAlphaFunction a N k α where
  toFun := periodicCAlphaTranslate h
  map_add' f g := by
    apply periodicCAlpha_toFun_injective
    funext x
    change (f + g).toFun (x + h) =
      (periodicCAlphaTranslate h f + periodicCAlphaTranslate h g).toFun x
    simp only [(periodicCAlpha_pointwise_operations a N k α).2.1, Pi.add_apply]
    rfl
  map_smul' c f := by
    apply periodicCAlpha_toFun_injective
    funext x
    change (c • f).toFun (x + h) = (c • periodicCAlphaTranslate h f).toFun x
    simp only [(periodicCAlpha_pointwise_operations a N k α).2.2, Pi.smul_apply]
    rfl
  norm_map' f := periodicCAlphaTranslate_norm h f

#print axioms periodicCAlphaTranslateIsometry

end GlobalEmbedding.Paper
