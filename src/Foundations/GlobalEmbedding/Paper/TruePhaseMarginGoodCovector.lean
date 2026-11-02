import GlobalEmbedding.Paper.GoodCovectorNormedCriterion
import GlobalEmbedding.Paper.TruePhaseMarginSpecification

open Bundle Manifold
open scoped TensorProduct ContDiff

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance positiveGoodSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance positiveGoodSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- The actual positive phase margin is equivalent to an actual unit good
covector in the source's norm-independent sense.

Proof: a positive attained maximum supplies a unit covector with positive
restricted minimum, hence an injective restriction. Conversely the compact
minimum for an injective unit restriction is positive and below the maximum.
Source: `defn:phase`, good covectors and the best-phase margin. -/
theorem true_phase_margin_positive_iff_unit_good_covector
    {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [RiemannianBundle (TangentSpace I : M → Type _)] {N : ℕ}
    (hdim : 2 ≤ Module.finrank ℝ E) (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M) :
    0 < truePhaseMargin f hf x ↔
      ∃ ξ : TangentSpace I x →L[ℝ] ℝ, ‖ξ‖ = 1 ∧ GoodCovector f hf x ξ := by
  have ht : 2 ≤ Module.finrank ℝ (TangentSpace I x) := by
    rwa [(tangentSpaceCastModel I x).toLinearEquiv.finrank_eq]
  constructor
  · intro hpos
    obtain ⟨ξ, hξ, hatt⟩ := (true_phase_margin_specification hdim f hf x).2.2.1
    have hp : 0 < leastSingularNorm (E := SymmetricSquare ξ.ker)
        (F := normalSpace (I := I) f x) (covectorRestriction (trueSecondFormL f hf x) ξ) := by
      rwa [hatt]
    have hi := (covector_restriction_bound ht (trueSecondFormL f hf x) ξ).2.2.mp hp
    have hne : ξ ≠ 0 := (norm_ne_zero_iff (a := ξ)).mp (ne_of_eq_of_ne hξ one_ne_zero)
    exact ⟨ξ, hξ, (good_covector_iff_normed f hf x ξ).mpr ⟨hne, hi⟩⟩
  · rintro ⟨ξ, hξ, hgood⟩
    have hi := ((good_covector_iff_normed f hf x ξ).mp hgood).2
    have hp := (covector_restriction_bound ht (trueSecondFormL f hf x) ξ).2.2.mpr hi
    have hle := (best_phase_supremum_specification ht (trueSecondFormL f hf x)).2.2.1 ξ hξ
    exact hp.trans_le hle

end GlobalEmbedding.Paper
