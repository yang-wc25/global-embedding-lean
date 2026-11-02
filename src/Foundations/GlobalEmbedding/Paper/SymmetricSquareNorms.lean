import GlobalEmbedding.Paper.SymmetricSquare
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Normed.Group.Quotient

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, second-jet comparison and preservation of the selector margin.
Norms are the canonical Hilbert tensor norm followed by the existing binary quotient norm. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

namespace SymmetricSquareNorms

-- Local projections select the canonical quotient norm structures consistently.
/-- The canonical Hilbert tensor quotient seminorm structure.
Source: `prop:initialization`, norms in symmetric-square transport. -/
@[instance_reducible]
noncomputable def squareSemi (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] : SeminormedAddCommGroup (SymmetricSquare V) :=
  Submodule.Quotient.seminormedAddCommGroup (symmetricSquareRelations V)
/-- The topology of the canonical quotient seminorm.
Source: `prop:initialization`, norms in symmetric-square transport. -/
@[instance_reducible]
noncomputable def squareTopology (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] : TopologicalSpace (SymmetricSquare V) :=
  (squareSemi V).toUniformSpace.toTopologicalSpace
/-- The additive structure inherited from the canonical quotient seminorm.
Source: `prop:initialization`, norms in symmetric-square transport. -/
@[instance_reducible]
noncomputable def squareAddMonoid (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] : AddCommMonoid (SymmetricSquare V) :=
  (squareSemi V).toAddCommMonoid
/-- The canonical real normed-space structure on the tensor quotient.
Source: `prop:initialization`, norms in symmetric-square transport. -/
@[instance_reducible]
noncomputable def squareNS (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] : NormedSpace ℝ (SymmetricSquare V) :=
  Submodule.Quotient.normedSpace (symmetricSquareRelations V) ℝ
/-- The real module structure inherited from the canonical quotient seminorm.
Source: `prop:initialization`, norms in symmetric-square transport. -/
@[instance_reducible]
noncomputable def squareModule (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] : Module ℝ (SymmetricSquare V) :=
  (squareNS V).toModule


end SymmetricSquareNorms
end GlobalEmbedding.Paper
