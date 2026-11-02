import GlobalEmbedding.Paper.PeriodicCAlphaDirectionalDerivativeLinear
import GlobalEmbedding.Paper.LittlePeriodicCAlphaSpace

/-!
# The actual bounded linear derivative on little periodic Hölder closures

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 399–418.
DAG node: `balanced-holder-little-directional-derivative`.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Restrict actual bounded differentiation from the ambient spaces to the actual little closures.

Differentiation preserves genuine smoothness, so the continuous ambient derivative maps
the source smooth closure into the target smooth closure. Restrict the domain and codomain
of that actual continuous linear map. Source: smooth approximation in `lem:balanced`. -/
noncomputable def littlePeriodicCAlphaDirectionalDerivative {a N k : ℕ} {α : ℝ}
    (v : EuclideanSpace ℝ (Fin a)) :
    LittlePeriodicCAlphaFunction a N (k + 1) α →L[ℝ] LittlePeriodicCAlphaFunction a N k α := by
  let D := periodicCAlphaDirectionalDerivativeLinear (N := N) (k := k) (α := α) v
  have hmaps : MapsTo D (smoothPeriodicCAlphaSubmodule a N (k + 1) α)
      (smoothPeriodicCAlphaSubmodule a N k α) := by
    intro f hf
    change ContDiff ℝ ∞ (fun x ↦ fderiv ℝ f.toFun x v)
    exact ((show ContDiff ℝ ∞ f.toFun from hf).fderiv_right (by simp)).clm_apply contDiff_const
  have hclosure := hmaps.closure D.continuous
  let D' := D.comp (smoothPeriodicCAlphaSubmodule a N (k + 1) α).topologicalClosure.subtypeL
  exact D'.codRestrict (smoothPeriodicCAlphaSubmodule a N k α).topologicalClosure
      (fun f ↦ hclosure f.property)

#print axioms littlePeriodicCAlphaDirectionalDerivative

end GlobalEmbedding.Paper
