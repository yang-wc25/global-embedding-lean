import GlobalEmbedding.Paper.PeriodicCAlphaRestrictOrderContinuous
import GlobalEmbedding.Paper.LittlePeriodicCAlphaSpace

/-!
# Bounded actual little Hölder regularity inclusion

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-little-restrict-order`.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Lowering order is an actual bounded linear map on the original little Hölder closures.

The actual ambient inclusion is continuous and keeps smooth lifts smooth. It therefore
maps their actual topological closures into each other. Restrict its values to these actual
closure subtypes and inherit linearity and the ambient operator norm bound. Source:
regularity levels in vertical translation derivatives in the proof of `lem:balanced`. -/
noncomputable def littlePeriodicCAlphaRestrictOrder {a N k : ℕ} {α : ℝ}
    (j : ℕ) (hj : j ≤ k) (hα : α ≤ 1) :
    LittlePeriodicCAlphaFunction a N k α →L[ℝ] LittlePeriodicCAlphaFunction a N j α := by
  let T := periodicCAlphaRestrictOrderContinuous (a := a) (N := N) j hj hα
  have hmaps : MapsTo T (smoothPeriodicCAlphaSubmodule a N k α : Set _)
      (smoothPeriodicCAlphaSubmodule a N j α : Set _) := by
    intro f hf
    change ContDiff ℝ ∞ (T f).toFun
    exact hf
  have hclosure := hmaps.closure T.continuous
  have hmem (f : LittlePeriodicCAlphaFunction a N k α) :
      T f.val ∈ (smoothPeriodicCAlphaSubmodule a N j α).topologicalClosure :=
    hclosure f.property
  let S : LittlePeriodicCAlphaFunction a N k α →ₗ[ℝ]
      LittlePeriodicCAlphaFunction a N j α :=
    { toFun := fun f ↦ ⟨T f.val, hmem f⟩
      map_add' := fun f g ↦ Subtype.ext (T.map_add f.val g.val)
      map_smul' := fun c f ↦ Subtype.ext (T.map_smul c f.val) }
  apply S.mkContinuous ‖T‖
  intro f
  exact T.le_opNorm f.val

#print axioms littlePeriodicCAlphaRestrictOrder

end GlobalEmbedding.Paper
