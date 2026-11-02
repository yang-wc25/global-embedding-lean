import GlobalEmbedding.Paper.FullTangentFrame
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Parallelizable smooth manifolds

Source: `literature/parallelizable-stable-plus-one/main.tex`, Section 7, Proposition
`prop:initialization`, lines 787–799. The proposition assumes a closed parallelizable source;
its proof uses a global tangent trivialization to obtain a smooth coframe. Here parallelizability
is represented by the existence of a full smooth tangent frame, together with the explicit real
model-dimension equality.
-/

namespace GlobalEmbedding.Paper

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `M` is parallelizable of dimension `n` when its real model space has dimension `n` and
it admits a full smooth tangent frame of length `n`. This predicate permits the empty manifold.
Source: `literature/parallelizable-stable-plus-one/main.tex`, Section 7, Proposition
`prop:initialization`, lines 787–799. -/
def IsParallelizable (n : ℕ) : Prop :=
  Module.finrank ℝ E = n ∧ Nonempty (FullTangentFrame I (M := M) n)

end GlobalEmbedding.Paper
