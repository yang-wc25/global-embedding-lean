import GlobalEmbedding.Paper.PeriodicCAlphaLinearClosure
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# The concrete submodule of periodic Hölder lifts

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-pointwise-submodule`.
-/

namespace GlobalEmbedding.Paper

/-- The function submodule consisting exactly of the lifts of actual periodic Hölder elements.

Its vector-space data use the proved pointwise closure of the actual carrier.
Source: `lem:balanced`, Hölder ambient-vector-space expansion. -/
def periodicCAlphaSubmodule (a N k : ℕ) (α : ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N)) where
  carrier := Set.range (fun f : PeriodicCAlphaFunction a N k α ↦ f.toFun)
  zero_mem' := (periodicCAlpha_linear_closure a N k α).1
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact (periodicCAlpha_linear_closure a N k α).2.1 f g
  smul_mem' := by
    rintro c _ ⟨f, rfl⟩
    exact (periodicCAlpha_linear_closure a N k α).2.2 c f

#print axioms periodicCAlphaSubmodule

end GlobalEmbedding.Paper
