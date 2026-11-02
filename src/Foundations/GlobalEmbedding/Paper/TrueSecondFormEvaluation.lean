import GlobalEmbedding.Paper.TrueSecondForm
import GlobalEmbedding.Paper.SymmetricBilinearDescendEvaluation

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, actual normal second form on the exact binary Sym² quotient. -/

open Manifold
open scoped TensorProduct ContDiff Topology
namespace GlobalEmbedding.Paper

/-- Evaluation of the actual true second form on the canonical product gives the
normal-valued centered Hessian, with exactly the project's quotient normalization.
Proof: apply the canonical symmetric bilinear descent evaluation theorem.
Source: `defn:phase`, B_F(v⊙w)=Π_F(∇²F(v,w)). -/
@[simp] theorem trueSecondForm_product
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M)
    (v w : TangentSpace I x) :
    trueSecondForm f hf x (symmetricSquareProduct (TangentSpace I x) v w) =
      centeredNormalHessian (I := I) f x v w := by
  exact symmetricBilinearDescend_product (centeredNormalHessian (I := I) f x)
    (centeredNormalHessian_symmetry (I := I) f hf x) v w

end GlobalEmbedding.Paper
