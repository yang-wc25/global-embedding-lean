import GlobalEmbedding.Paper.PeriodicCAlphaSubmodule
import GlobalEmbedding.Paper.PeriodicCAlphaCarrierInjective

/-!
# Identifying the periodic Hölder carrier with its concrete function submodule

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-carrier-equivalence`.
-/

namespace GlobalEmbedding.Paper

/-- The raw periodic Hölder carrier is canonically equivalent to its submodule of actual lifts.

The forward map preserves the actual function. The inverse chooses its unique carrier
representative, whose underlying function is prescribed by membership in the range.
Source: `lem:balanced`, Hölder ambient-vector-space expansion. -/
noncomputable def periodicCAlphaCarrierEquiv (a N k : ℕ) (α : ℝ) :
    PeriodicCAlphaFunction a N k α ≃ periodicCAlphaSubmodule a N k α where
  toFun f := ⟨f.toFun, ⟨f, rfl⟩⟩
  invFun f := Classical.choose f.property
  left_inv f := periodicCAlpha_toFun_injective (Classical.choose_spec
    (show ∃ g : PeriodicCAlphaFunction a N k α, g.toFun = f.toFun from ⟨f, rfl⟩))
  right_inv f := Subtype.ext (Classical.choose_spec f.property)

#print axioms periodicCAlphaCarrierEquiv

end GlobalEmbedding.Paper
