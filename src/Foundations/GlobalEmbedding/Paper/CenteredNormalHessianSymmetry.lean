import GlobalEmbedding.Paper.SecondFormChartInvarianceGeneral

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, actual normal second form on the exact binary Sym² quotient. -/

open Manifold
open scoped TensorProduct ContDiff Topology
namespace GlobalEmbedding.Paper

/-- The actual centered normal Hessian of a smooth Euclidean-valued map is symmetric.
Proof: global C∞ implies C² at x, then use the already proved arbitrary-model chart
and connection theorem. This is the named well-definedness proof for trueSecondForm.
Source: `defn:phase`, symmetric-square realization of the true normal second form. -/
theorem centeredNormalHessian_symmetry
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M) :
    ∀ v w : TangentSpace I x,
      centeredNormalHessian (I := I) f x v w =
        centeredNormalHessian (I := I) f x w v := by
  have hf2 : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 2 f x :=
    (hf x).of_le (by norm_num)
  exact (second_form_chart_invariance_general f x hf2).1

end GlobalEmbedding.Paper
