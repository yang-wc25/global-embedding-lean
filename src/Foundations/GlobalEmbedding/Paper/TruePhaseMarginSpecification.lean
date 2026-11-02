import GlobalEmbedding.Paper.TruePhaseMargin
import GlobalEmbedding.Paper.BestPhaseMaximumAttainment

open Bundle Manifold
open scoped TensorProduct ContDiff

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance trueSpecSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance trueSpecSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- The actual true-second-form phase margin has exactly the source maximum
and is unchanged by ambient inclusion of the actual normal space.

Proof: apply the actual restriction supremum and maximum theorems to the actual
normal-valued trueSecondFormL. The normal-space norm is the induced ambient norm,
so ambient inclusion gives identical unit-sphere norm images, infima and supremum.
Source: `defn:phase`, best-phase margin with induced norms. -/
theorem true_phase_margin_specification
    {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [RiemannianBundle (TangentSpace I : M → Type _)] {N : ℕ}
    (hdim : 2 ≤ Module.finrank ℝ E) (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M) :
    0 ≤ truePhaseMargin f hf x ∧ truePhaseMargin f hf x ≤ ‖trueSecondFormL f hf x‖ ∧
    (∃ ξ : TangentSpace I x →L[ℝ] ℝ, ‖ξ‖ = 1 ∧
      leastSingularNorm (E := SymmetricSquare ξ.ker) (F := normalSpace (I := I) f x)
        (covectorRestriction (trueSecondFormL f hf x) ξ) = truePhaseMargin f hf x) ∧
    (∀ S : SymmetricSquare (TangentSpace I x) →L[ℝ] EuclideanSpace ℝ (Fin N),
      S.toLinearMap = (normalSpace (I := I) f x).subtype.comp (trueSecondForm f hf x) →
      bestPhaseSupremum S = truePhaseMargin f hf x) := by
  have ht : 2 ≤ Module.finrank ℝ (TangentSpace I x) := by
    rwa [(tangentSpaceCastModel I x).toLinearEquiv.finrank_eq]
  have hspec := best_phase_supremum_specification ht (trueSecondFormL f hf x)
  refine ⟨hspec.1, hspec.2.1, best_phase_maximum_attainment ht (trueSecondFormL f hf x), ?_⟩
  intro S hS
  have he : S = (normalSpace (I := I) f x).subtypeL.comp (trueSecondFormL f hf x) := by
    apply ContinuousLinearMap.ext
    intro z
    exact congrArg (fun t : SymmetricSquare (TangentSpace I x) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin N) ↦ t z) hS
  rw [he]
  rfl

end GlobalEmbedding.Paper
