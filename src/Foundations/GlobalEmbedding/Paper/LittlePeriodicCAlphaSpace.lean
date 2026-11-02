import GlobalEmbedding.Paper.SmoothPeriodicCAlphaSubmodule
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Group.Submodule

/-!
# The actual little periodic Hölder space

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder`.
-/

namespace GlobalEmbedding.Paper

/-- The little periodic Hölder space is the closure of smooth lifts in the actual periodic
Hölder normed space, with its inherited operations and norm.

This is the actual closure subtype; no completed replacement or assumed Banach model is
used. Completeness is a separate theorem. Source: `lem:balanced`, proof, line 382. -/
abbrev LittlePeriodicCAlphaFunction (a N k : ℕ) (α : ℝ) :=
  ↥((smoothPeriodicCAlphaSubmodule a N k α).topologicalClosure)

#print axioms LittlePeriodicCAlphaFunction

end GlobalEmbedding.Paper
