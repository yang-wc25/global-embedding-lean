import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
`prop:initialization` proof, full Cj inverse/projection comparison.
The derivative suprema below are used with explicit boundedness hypotheses. -/

namespace GlobalEmbedding.Paper

/-- The sum of actual suprema of iterated Fréchet derivative operator norms through
order j over U. The inserted zero gives zero for the empty domain. Boundedness of
each derivative-norm range is supplied explicitly in theorems using this quantity.
Source: `prop:initialization` proof, line822, quantitative inverse dependence. -/
noncomputable def finiteCjNorm
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) (f : D → F) (U : Set D) : ℝ :=
  ∑ k ∈ Finset.range (j + 1),
    sSup (insert 0 (Set.range fun x : U ↦ ‖iteratedFDeriv ℝ k f x‖))

end GlobalEmbedding.Paper
