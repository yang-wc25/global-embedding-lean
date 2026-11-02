import GlobalEmbedding.Paper.PeriodicCAlphaNormDefinite
import GlobalEmbedding.Paper.PeriodicCAlphaNormNonnegative
import GlobalEmbedding.Paper.PeriodicCAlphaNormTriangle
import GlobalEmbedding.Paper.PeriodicCAlphaNormHomogeneity
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The actual normed additive group of periodic Hölder functions

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-norm-axioms`.
-/

namespace GlobalEmbedding.Paper

/-- The carrier norm is exactly the previously defined real Hölder formula.
Source: `lem:balanced`, usual periodic Hölder norm expansion. -/
noncomputable instance periodicCAlphaNormInst {a N k : ℕ} {α : ℝ} :
    Norm (PeriodicCAlphaFunction a N k α) := ⟨periodicCAlphaNorm⟩

/-- The actual periodic Hölder formula satisfies the normed-vector-space core axioms.

Proof: use the proved nonnegativity, triangle and homogeneity statements for the actual
vector-space operations. Definiteness follows from the value bound and injectivity of the
underlying-function projection, whose zero operation is pointwise zero.
Source: `lem:balanced`, usual periodic Hölder norm expansion. -/
theorem periodicCAlphaNormedCore {a N k : ℕ} {α : ℝ} :
    NormedSpace.Core ℝ (PeriodicCAlphaFunction a N k α) where
  norm_nonneg := periodicCAlphaNorm_nonnegative
  norm_smul := periodicCAlphaNorm_homogeneous
  norm_triangle := periodicCAlphaNorm_triangle
  norm_eq_zero_iff f := by
    change periodicCAlphaNorm f = 0 ↔ f = 0
    rw [periodicCAlphaNorm_eq_zero_iff]
    constructor
    · intro h
      apply periodicCAlpha_toFun_injective
      exact h.trans (periodicCAlpha_pointwise_operations a N k α).1.symm
    · intro h
      rw [h]
      exact (periodicCAlpha_pointwise_operations a N k α).1

/-- The normed additive group on the actual periodic Hölder carrier.

Its norm, distance and topology are constructed from the fully proved norm core, not from
any assumed function-space model. Source: `lem:balanced`, Hölder ambient-space expansion. -/
noncomputable instance periodicCAlphaNormedAddCommGroup {a N k : ℕ} {α : ℝ} :
    NormedAddCommGroup (PeriodicCAlphaFunction a N k α) :=
  NormedAddCommGroup.ofCore periodicCAlphaNormedCore

#print axioms periodicCAlphaNormInst
#print axioms periodicCAlphaNormedCore
#print axioms periodicCAlphaNormedAddCommGroup

end GlobalEmbedding.Paper
