import GlobalEmbedding.Paper.PeriodicCAlphaCarrierEquiv
import Mathlib.Algebra.Module.TransferInstance

/-!
# The actual pointwise vector space of periodic Hölder functions

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-pointwise-vector-space`.
-/

namespace GlobalEmbedding.Paper

/-- The additive group on the actual carrier, transferred from its concrete function submodule.
Source: `lem:balanced`, Hölder ambient-vector-space expansion. -/
noncomputable instance periodicCAlphaAddCommGroup {a N k : ℕ} {α : ℝ} :
    AddCommGroup (PeriodicCAlphaFunction a N k α) :=
  (periodicCAlphaCarrierEquiv a N k α).addCommGroup

/-- The real module on the actual carrier, transferred from its concrete function submodule.
Source: `lem:balanced`, Hölder ambient-vector-space expansion. -/
noncomputable instance periodicCAlphaModule {a N k : ℕ} {α : ℝ} :
    Module ℝ (PeriodicCAlphaFunction a N k α) :=
  (periodicCAlphaCarrierEquiv a N k α).addEquiv.module ℝ

#print axioms periodicCAlphaAddCommGroup
#print axioms periodicCAlphaModule

end GlobalEmbedding.Paper
