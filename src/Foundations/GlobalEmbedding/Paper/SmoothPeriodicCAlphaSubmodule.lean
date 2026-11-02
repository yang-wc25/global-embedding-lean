import GlobalEmbedding.Paper.PeriodicCAlphaSpace
import GlobalEmbedding.Paper.PeriodicCAlphaPointwiseOperations
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The smooth submodule inside the actual periodic Hölder space

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-smooth-submodule`.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The submodule of actual periodic Hölder elements whose Euclidean lifts are smooth.

Its operations are the already constructed pointwise operations on the actual carrier;
classical smoothness is preserved by zero, addition and real scalar multiplication.
Source: `lem:balanced`, definition of little Hölder as the smooth closure. -/
def smoothPeriodicCAlphaSubmodule (a N k : ℕ) (α : ℝ) :
    Submodule ℝ (PeriodicCAlphaFunction a N k α) where
  carrier := {f | ContDiff ℝ ∞ f.toFun}
  zero_mem' := by
    change ContDiff ℝ ∞ (0 : PeriodicCAlphaFunction a N k α).toFun
    rw [(periodicCAlpha_pointwise_operations a N k α).1]
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ (f + g).toFun
    rw [(periodicCAlpha_pointwise_operations a N k α).2.1 f g]
    exact (show ContDiff ℝ ∞ f.toFun from hf).add
      (show ContDiff ℝ ∞ g.toFun from hg)
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ ∞ (c • f).toFun
    rw [(periodicCAlpha_pointwise_operations a N k α).2.2 c f]
    exact (show ContDiff ℝ ∞ f.toFun from hf).const_smul c

#print axioms smoothPeriodicCAlphaSubmodule

end GlobalEmbedding.Paper
