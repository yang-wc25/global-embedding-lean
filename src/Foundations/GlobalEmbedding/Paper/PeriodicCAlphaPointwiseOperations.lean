import GlobalEmbedding.Paper.PeriodicCAlphaVectorSpace

/-!
# Pointwise equations for the periodic Hölder vector-space operations

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-pointwise-operations`.
-/

namespace GlobalEmbedding.Paper

/-- The actual carrier's zero, sum and scalar multiplication have their prescribed pointwise
underlying functions.

Proof: the carrier equivalence is the identity on underlying functions and the transferred
additive/linear equivalences preserve zero, addition and real scalar multiplication.
Source: `lem:balanced`, Hölder ambient-vector-space expansion. -/
theorem periodicCAlpha_pointwise_operations (a N k : ℕ) (α : ℝ) :
    (0 : PeriodicCAlphaFunction a N k α).toFun = 0 ∧
    (∀ f g : PeriodicCAlphaFunction a N k α, (f + g).toFun = f.toFun + g.toFun) ∧
    (∀ (c : ℝ) (f : PeriodicCAlphaFunction a N k α), (c • f).toFun = c • f.toFun) := by
  let e := periodicCAlphaCarrierEquiv a N k α
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun z : periodicCAlphaSubmodule a N k α ↦ z.val) e.addEquiv.map_zero
  · intro f g
    exact congrArg (fun z : periodicCAlphaSubmodule a N k α ↦ z.val)
      (e.addEquiv.map_add f g)
  · intro c f
    exact congrArg (fun z : periodicCAlphaSubmodule a N k α ↦ z.val)
      ((e.addEquiv.linearEquiv ℝ).map_smul c f)

#print axioms periodicCAlpha_pointwise_operations

end GlobalEmbedding.Paper
