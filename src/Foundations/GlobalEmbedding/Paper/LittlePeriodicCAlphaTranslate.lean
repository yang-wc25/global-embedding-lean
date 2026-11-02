import GlobalEmbedding.Paper.PeriodicCAlphaTranslateIsometry
import GlobalEmbedding.Paper.LittlePeriodicCAlphaSpace

/-!
# Translation on the actual little periodic Hölder closure

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-little-translation-isometry`.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Restrict actual translation to the little Hölder closure as a real linear isometry.

Translation preserves smoothness by composition with x↦x+h. The ambient linear isometry
is continuous, so it maps the closure of the smooth submodule into itself. Its restriction
inherits exact norm preservation and pointwise operations.
Source: little Hölder translation in the proof of `lem:balanced`. -/
noncomputable def littlePeriodicCAlphaTranslateIsometry {a N k : ℕ} {α : ℝ}
    (h : EuclideanSpace ℝ (Fin a)) :
    LittlePeriodicCAlphaFunction a N k α →ₗᵢ[ℝ] LittlePeriodicCAlphaFunction a N k α := by
  let T := periodicCAlphaTranslateIsometry (N := N) (k := k) (α := α) h
  have hmaps : MapsTo T (smoothPeriodicCAlphaSubmodule a N k α)
      (smoothPeriodicCAlphaSubmodule a N k α) := by
    intro f hf
    change ContDiff ℝ ∞ (fun x ↦ f.toFun (x + h))
    exact (show ContDiff ℝ ∞ f.toFun from hf).comp (contDiff_id.add contDiff_const)
  have hclosure := hmaps.closure T.continuous
  exact
    { toFun := fun f ↦ ⟨T f.val, hclosure f.property⟩
      map_add' := fun f g ↦ Subtype.ext (T.map_add f.val g.val)
      map_smul' := fun c f ↦ Subtype.ext (T.map_smul c f.val)
      norm_map' := fun f ↦ T.norm_map f.val }

#print axioms littlePeriodicCAlphaTranslateIsometry

end GlobalEmbedding.Paper
