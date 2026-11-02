import GlobalEmbedding.Paper.TrueSecondFormEvaluation

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, actual normal second form on the exact binary Sym² quotient. -/

open Manifold
open scoped TensorProduct ContDiff Topology
namespace GlobalEmbedding.Paper

/-- In every maximal C² atlas chart, the projected coordinate Hessian on actual chart
differentials equals the actual true second form on the canonical product.
Proof: C∞ implies C² at x; use the general-I chart theorem and product evaluation.
Source: `defn:phase`, coordinate realization of the normal second form. -/
theorem trueSecondForm_chart
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M)
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I 2 M)
    (hx : x ∈ e.source) (v w : TangentSpace I x) :
    (normalSpace (I := I) f x).orthogonalProjectionOnto
      (fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm)) (e.extend I x)
        (tangentSpaceCastModel 𝓘(ℝ, E) (e.extend I x)
          (mfderiv I 𝓘(ℝ, E) (e.extend I) x v))
        (tangentSpaceCastModel 𝓘(ℝ, E) (e.extend I x)
          (mfderiv I 𝓘(ℝ, E) (e.extend I) x w))) =
      trueSecondForm f hf x (symmetricSquareProduct (TangentSpace I x) v w) := by
  have hf2 : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 2 f x :=
    (hf x).of_le (by norm_num)
  rw [trueSecondForm_product]
  exact (second_form_chart_invariance_general f x hf2).2.1 e he hx v w

end GlobalEmbedding.Paper
