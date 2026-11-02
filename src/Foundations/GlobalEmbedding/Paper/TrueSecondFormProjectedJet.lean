import GlobalEmbedding.Paper.TrueSecondFormEvaluation

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition
`defn:phase` and Proposition `prop:initialization`, actual coordinate-jet interpretation. -/

open Manifold
open scoped TensorProduct ContDiff Topology
namespace GlobalEmbedding.Paper

/-- If Q has the source coordinate second-derivative values on quotient products,
its normal projection is the ambient inclusion of the actual entire true-second-form
operator. Equality is on the exact binary quotient, not just a bilinear comparison.

Proof: compose both quotient maps with the quotient projection. Tensor product
extensionality reduces equality to pure tensors; apply the actual product formula
for trueSecondForm and the stated coordinate-jet values of Q.
Source: `prop:initialization`, identification of projected coordinate jets with true
normal second forms, using Definition `defn:phase`. -/
theorem trueSecondForm_eq_projected_coordinate_jet
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M)
    (Q : SymmetricSquare (TangentSpace I x) →ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    (hQ : ∀ v w, Q (symmetricSquareProduct (TangentSpace I x) v w) =
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x)
        (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w)) :
    (normalSpace (I := I) f x).subtype.comp (trueSecondForm f hf x) =
      (normalSpace (I := I) f x).starProjection.toLinearMap.comp Q := by
  apply (symmetricSquareRelations (TangentSpace I x)).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change (trueSecondForm f hf x (symmetricSquareProduct (TangentSpace I x) v w) :
      EuclideanSpace ℝ (Fin N)) =
    (normalSpace (I := I) f x).starProjection
      (Q (symmetricSquareProduct (TangentSpace I x) v w))
  rw [trueSecondForm_product, hQ]
  rfl

end GlobalEmbedding.Paper
