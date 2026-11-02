import GlobalEmbedding.Paper.CovectorUpperSemicontinuity
import GlobalEmbedding.Paper.BestPhaseSupremumSpecification

open scoped TensorProduct

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance maxSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance maxSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- The actual best-phase margin is attained on the actual unit-covector sphere.
Thus its supremum definition equals the maximum in `defn:phase`.

Proof: the sphere is nonempty compact and the actual restriction minimum is
upper semicontinuous there. Its maximum bounds every value, and the actual
supremum specification identifies that maximum with the supremum. -/
theorem best_phase_maximum_attainment
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hdim : 2 ≤ Module.finrank ℝ E) (S : SymmetricSquare E →L[ℝ] F) :
    ∃ ξ : E →L[ℝ] ℝ, ‖ξ‖ = 1 ∧
      leastSingularNorm (E := SymmetricSquare ξ.ker) (F := F) (covectorRestriction S ξ) =
        bestPhaseSupremum S := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  have : Nontrivial (E →L[ℝ] ℝ) := (InnerProductSpace.toDualMap ℝ E).injective.nontrivial
  have hne : (Metric.sphere (0 : E →L[ℝ] ℝ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  let f := fun ξ : E →L[ℝ] ℝ ↦
    leastSingularNorm (E := SymmetricSquare ξ.ker) (F := F) (covectorRestriction S ξ)
  have hsc : UpperSemicontinuousOn f (Metric.sphere (0 : E →L[ℝ] ℝ) 1) := by
    intro ξ hξ
    have hn : ‖ξ‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hξ
    have hξ0 : ξ ≠ 0 := by intro he; simp [he] at hn
    exact (covector_upper_semicontinuity hdim S ξ hξ0).upperSemicontinuousWithinAt _
  obtain ⟨ξ, hξ, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn hne
    (isCompact_sphere (0 : E →L[ℝ] ℝ) 1) hsc
  have hn : ‖ξ‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hξ
  refine ⟨ξ, hn, le_antisymm ((best_phase_supremum_specification hdim S).2.2.1 ξ hn) ?_⟩
  apply csSup_le (hne.image f)
  rintro _ ⟨η, hη, rfl⟩
  exact hmax hη

end GlobalEmbedding.Paper
