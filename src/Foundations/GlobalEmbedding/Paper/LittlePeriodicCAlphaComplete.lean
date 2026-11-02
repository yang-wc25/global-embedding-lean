import GlobalEmbedding.Paper.PeriodicCAlphaComplete
import GlobalEmbedding.Paper.LittlePeriodicCAlphaSpace

/-!
# Completeness of the actual little periodic Hölder space

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-little-complete`.
-/

namespace GlobalEmbedding.Paper

/-- The actual little periodic Hölder closure is complete in the inherited actual Hölder norm.

Proof: the actual ambient space is complete by the proved ambient theorem. The little space
is the actual topological closure of the smooth submodule, hence closed. Apply Mathlib's
closed-subspace completeness theorem to that subtype. No independent Banach assumption or
completed replacement is used. Source: `lem:balanced`, little-Hölder-space expansion. -/
theorem littlePeriodicCAlpha_completeSpace (a N k : ℕ) (α : ℝ) :
    CompleteSpace (LittlePeriodicCAlphaFunction a N k α) :=
  (smoothPeriodicCAlphaSubmodule a N k α).isClosed_topologicalClosure.completeSpace_coe

/-- The complete-space instance for the actual little periodic Hölder closure.
Source: `lem:balanced`, proved by the named closed-subspace completeness theorem. -/
instance littlePeriodicCAlphaCompleteSpace {a N k : ℕ} {α : ℝ} :
    CompleteSpace (LittlePeriodicCAlphaFunction a N k α) :=
  littlePeriodicCAlpha_completeSpace a N k α

#print axioms littlePeriodicCAlpha_completeSpace
#print axioms littlePeriodicCAlphaCompleteSpace

end GlobalEmbedding.Paper
