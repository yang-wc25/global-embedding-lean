import GlobalEmbedding.Paper.TrueSecondForm
import GlobalEmbedding.Paper.SymmetricSquareLinearMap

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- An actual covector is good when it is nonzero and the actual normal-valued
true second form is injective on the symmetric square of its literal kernel.
This definition uses the canonical algebraic inclusion and has no auxiliary
metric or norm parameter. In finite dimension all real covectors are continuous.
Source: `literature/parallelizable-stable-plus-one/main.tex`, `defn:phase`. -/
def GoodCovector
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : Prop :=
  ξ ≠ 0 ∧ Function.Injective
    ((trueSecondForm f hf x).comp (symmetricSquareLinearMap ξ.ker.subtype))

end GlobalEmbedding.Paper
