import GlobalEmbedding.Paper.LittlePeriodicCAlphaSpace
import Mathlib.Topology.Constructions

/-!
# Actual smooth elements are dense in the actual little Hölder closure

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 382.
DAG node: `balanced-holder-smooth-dense`.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Actual smooth lifts form a dense subset of the actual little Hölder space.

Proof: the image of this subset under the closure-subtype inclusion is exactly the smooth
submodule. The subtype density criterion is then precisely membership in its closure.
Source: the smooth-closure definition in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_smooth_dense (a N k : ℕ) (α : ℝ) :
    Dense {f : LittlePeriodicCAlphaFunction a N k α | ContDiff ℝ ∞ f.val.toFun} := by
  intro f
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hf : f.val ∈ closure
      (smoothPeriodicCAlphaSubmodule a N k α : Set (PeriodicCAlphaFunction a N k α)) := f.property
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf ε hε
  exact ⟨⟨g, (smoothPeriodicCAlphaSubmodule a N k α).le_topologicalClosure hg⟩, hg, hfg⟩

#print axioms littlePeriodicCAlpha_smooth_dense

end GlobalEmbedding.Paper
