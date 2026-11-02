import GlobalEmbedding.Paper.BestPhaseSupremum
import GlobalEmbedding.Paper.CovectorRestrictionBound
import Mathlib.Analysis.InnerProductSpace.Dual

open scoped TensorProduct

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance specSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance specSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- The actual best-phase supremum is finite and dominates every unit-covector
lower bound. Maximum attainment is a separate obligation.

Proof: the actual unit-covector sphere is nonempty by the Riesz embedding. Each
actual restricted minimum is nonnegative and bounded by the whole operator norm.
Apply the actual conditional supremum rules and the homogeneous lower-bound
characterization. Source: `defn:phase`, best-phase margin. -/
theorem best_phase_supremum_specification
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hdim : 2 ≤ Module.finrank ℝ E) (S : SymmetricSquare E →L[ℝ] F) :
    0 ≤ bestPhaseSupremum S ∧ bestPhaseSupremum S ≤ ‖S‖ ∧
    (∀ ξ : E →L[ℝ] ℝ, ‖ξ‖ = 1 →
      leastSingularNorm (E := SymmetricSquare ξ.ker) (F := F) (covectorRestriction S ξ) ≤
        bestPhaseSupremum S) ∧
    (∀ (ξ : E →L[ℝ] ℝ) (m : ℝ), ‖ξ‖ = 1 →
      (∀ z, m * ‖z‖ ≤ ‖covectorRestriction S ξ z‖) → m ≤ bestPhaseSupremum S) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  have : Nontrivial (E →L[ℝ] ℝ) := (InnerProductSpace.toDualMap ℝ E).injective.nontrivial
  have hne : (Metric.sphere (0 : E →L[ℝ] ℝ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  let f := fun ξ : E →L[ℝ] ℝ ↦
    leastSingularNorm (E := SymmetricSquare ξ.ker) (F := F) (covectorRestriction S ξ)
  have hbdd : BddAbove (f '' Metric.sphere (0 : E →L[ℝ] ℝ) 1) := by
    refine ⟨‖S‖, ?_⟩
    rintro _ ⟨ξ, _, rfl⟩
    exact (covector_restriction_bound hdim S ξ).2.1
  have hupper : bestPhaseSupremum S ≤ ‖S‖ := by
    apply csSup_le (hne.image f)
    rintro _ ⟨ξ, _, rfl⟩
    exact (covector_restriction_bound hdim S ξ).2.1
  have hentry : ∀ ξ : E →L[ℝ] ℝ, ‖ξ‖ = 1 → f ξ ≤ bestPhaseSupremum S := by
    intro ξ hξ
    apply le_csSup hbdd
    exact ⟨ξ, by simpa [Metric.mem_sphere, dist_zero_right] using hξ, rfl⟩
  have hzero : 0 ≤ bestPhaseSupremum S := by
    obtain ⟨ξ, hξ⟩ := hne
    have hξ1 : ‖ξ‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hξ
    exact (covector_restriction_bound hdim S ξ).1.trans (hentry ξ hξ1)
  refine ⟨hzero, hupper, hentry, ?_⟩
  intro ξ m hξ hm
  have : Nontrivial ξ.ker := covector_kernel_nontrivial hdim ξ
  have : Nontrivial (SymmetricSquare ξ.ker) := symmetric_square_nontrivial
  have he := (least_singular_norm_bound (E := SymmetricSquare ξ.ker) (F := F)
    (covectorRestriction S ξ)).2.2 m |>.mpr hm
  exact he.trans (hentry ξ hξ)

end GlobalEmbedding.Paper
