import GlobalEmbedding.Paper.CovectorRestriction
import GlobalEmbedding.Paper.LeastSingularNormAttainment
import GlobalEmbedding.Paper.SymmetricSquareSubspaceIsometry
import GlobalEmbedding.Paper.SymmetricSquareNontrivial
import GlobalEmbedding.Paper.CovectorKernelNontrivial

open scoped TensorProduct

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance boundSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance boundSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- The actual covector restriction has a finite nonnegative least singular norm,
bounded by the norm of the entire operator, and positive precisely for injective
restriction.

Proof: dimension at least two makes the actual kernel and its symmetric square
nontrivial. Compact sphere attainment gives the minimum and positivity criterion;
the proved isometric symmetric-square inclusion bounds the minimum by the ambient
operator norm. Source: `defn:phase`, quantitative goodness of a covector. -/
theorem covector_restriction_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hdim : 2 ≤ Module.finrank ℝ E) (S : SymmetricSquare E →L[ℝ] F)
    (ξ : E →L[ℝ] ℝ) :
    0 ≤ leastSingularNorm (E := SymmetricSquare ξ.ker) (F := F) (covectorRestriction S ξ) ∧
    leastSingularNorm (E := SymmetricSquare ξ.ker) (F := F) (covectorRestriction S ξ) ≤ ‖S‖ ∧
    (0 < leastSingularNorm (E := SymmetricSquare ξ.ker) (F := F) (covectorRestriction S ξ) ↔
      Function.Injective (covectorRestriction S ξ)) := by
  have : Nontrivial ξ.ker := covector_kernel_nontrivial hdim ξ
  have : Nontrivial (SymmetricSquare ξ.ker) := symmetric_square_nontrivial
  let R : SymmetricSquare ξ.ker →L[ℝ] F := covectorRestriction S ξ
  change 0 ≤ leastSingularNorm (E := SymmetricSquare ξ.ker) (F := F) R ∧ leastSingularNorm (E := SymmetricSquare ξ.ker) (F := F) R ≤ ‖S‖ ∧
    (0 < leastSingularNorm (E := SymmetricSquare ξ.ker) (F := F) R ↔ Function.Injective R)
  have hspec := least_singular_norm_attainment (E := SymmetricSquare ξ.ker) (F := F) R
  have hlow := least_singular_norm_bound (E := SymmetricSquare ξ.ker) (F := F) R
  obtain ⟨z, hz, hval⟩ := hspec.1
  refine ⟨hlow.1, ?_, hspec.2.2⟩
  rw [← hval]
  change ‖S (symmetricSquareMapL ξ.ker.subtypeL z)‖ ≤ ‖S‖
  have he := S.le_opNorm (symmetricSquareMapL ξ.ker.subtypeL z)
  rw [symmetric_square_subspace_isometry ξ.ker z, hz, mul_one] at he
  exact he

end GlobalEmbedding.Paper
