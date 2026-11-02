import GlobalEmbedding.Paper.SymmetricSquareMapNorm
import GlobalEmbedding.Paper.SymmetricSquareMapComposition
import GlobalEmbedding.Paper.SymmetricSquareMapIdentity
import GlobalEmbedding.Paper.SymmetricSquareMapLEval
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open scoped TensorProduct

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance squareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance squareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- A subspace's actual canonical symmetric-square quotient norm agrees with the
norm induced by its inclusion in the ambient symmetric square.

Proof: inclusion and orthogonal retraction are contractions, so their actual
induced maps are contractions. Their composition is the identity by functoriality,
which proves the reverse inequality. Source: `defn:phase`, induced hyperplane norms. -/
theorem symmetric_square_subspace_isometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (H : Submodule ℝ E) :
    ∀ z : SymmetricSquare H, ‖symmetricSquareMapL H.subtypeL z‖ = ‖z‖ := by
  have hinc : ∀ z : SymmetricSquare H, ‖symmetricSquareMap H.subtypeL z‖ ≤ ‖z‖ := by
    intro z
    refine (symmetricSquareMap_norm_le H.subtypeL z).trans ?_
    have hn : ‖H.subtypeL‖ ^ 2 ≤ (1 : ℝ) := by
      nlinarith [H.norm_subtypeL_le, norm_nonneg H.subtypeL]
    simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg z)
  have hproj : ∀ z : SymmetricSquare E,
      ‖symmetricSquareMap H.orthogonalProjectionOnto z‖ ≤ ‖z‖ := by
    intro z
    refine (symmetricSquareMap_norm_le H.orthogonalProjectionOnto z).trans ?_
    have hn : ‖H.orthogonalProjectionOnto‖ ^ 2 ≤ (1 : ℝ) := by
      nlinarith [H.orthogonalProjectionOnto_norm_le, norm_nonneg H.orthogonalProjectionOnto]
    simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg z)
  have hcomp : H.orthogonalProjectionOnto.comp H.subtypeL = ContinuousLinearMap.id ℝ H := by
    ext v
    simp
  intro z
  rw [symmetricSquareMapL_apply]
  apply le_antisymm (hinc z)
  have he := hproj (symmetricSquareMap H.subtypeL z)
  rw [symmetricSquareMap_comp, hcomp, symmetricSquareMap_id] at he
  exact he

end GlobalEmbedding.Paper
