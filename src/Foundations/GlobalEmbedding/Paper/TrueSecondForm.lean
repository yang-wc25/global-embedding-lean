import GlobalEmbedding.Paper.SecondFormSymmetricQuotient
import GlobalEmbedding.Paper.CenteredNormalHessianSymmetry

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, actual normal second form on the exact binary Sym² quotient. -/

open Manifold
open scoped TensorProduct ContDiff Topology
namespace GlobalEmbedding.Paper

/-- The true normal second form on the exact binary symmetric square of the tangent
space, with values in the actual normal-space subtype.

Its honest data are the canonical descent of centeredNormalHessian; the named
symmetry theorem proves well-definedness. Smoothness is explicit as C∞ of f, and
C² needed for symmetry is derived from it. No immersion assumption is necessary to
construct this stronger object, so every source smooth immersion is included.
Source: `defn:phase`, B_F:Sym²(T_xM)→ν_F(x), with no factor 1/2 inserted. -/
noncomputable def trueSecondForm
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M) :
    SymmetricSquare (TangentSpace I x) →ₗ[ℝ] normalSpace (I := I) f x :=
  symmetricBilinearDescend (centeredNormalHessian (I := I) f x)
    (centeredNormalHessian_symmetry (I := I) f hf x)

end GlobalEmbedding.Paper
