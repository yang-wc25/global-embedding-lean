import GlobalEmbedding.Offline.GoodDictionaryMargins
import GlobalEmbedding.Paper.BestPhaseMaximumAttainment
import GlobalEmbedding.Paper.LeastSingularNormPerturbation
import GlobalEmbedding.Paper.SymmetricSquareSubspaceIsometry

/-!
# Continuity and compact superlevel sets of the actual best-phase margin

The existing best-phase supremum is 1-Lipschitz in the actual whole second-form
operator norm.  Each literal symmetric-square kernel inclusion is isometric,
and the already proved least-singular-norm perturbation estimate applies on that
same kernel.  Consequently a bounded positive-margin class of actual second
forms is compact, and every member has a genuine original good covector.
-/

open GlobalEmbedding.Paper
open scoped Topology TensorProduct

namespace GlobalEmbedding.Offline

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance phaseLipschitzRelationsClosed {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    IsClosed (symmetricSquareRelations V : Set (V ⊗[ℝ] V)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance phaseLipschitzSquareNormed {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    NormedAddCommGroup (SymmetricSquare V) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations V)

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem covectorRestriction_norm_sub_le
    (S T : SymmetricSquare V →L[ℝ] F) (ξ : V →L[ℝ] ℝ) :
    ‖covectorRestriction S ξ - covectorRestriction T ξ‖ ≤ ‖S - T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  change ‖(S - T) (symmetricSquareMapL ξ.ker.subtypeL z)‖ ≤ ‖S - T‖ * ‖z‖
  have h := (S - T).le_opNorm (symmetricSquareMapL ξ.ker.subtypeL z)
  rwa [symmetric_square_subspace_isometry ξ.ker z] at h

theorem bestPhaseSupremum_sub_le
    (hdim : 2 ≤ Module.finrank ℝ V) (S T : SymmetricSquare V →L[ℝ] F) :
    bestPhaseSupremum S - bestPhaseSupremum T ≤ ‖S - T‖ := by
  obtain ⟨ξ, hξ, he⟩ := best_phase_maximum_attainment hdim S
  let : Nontrivial ξ.ker := covector_kernel_nontrivial hdim ξ
  let : Nontrivial (SymmetricSquare ξ.ker) := symmetric_square_nontrivial
  have h := (least_singular_norm_perturbation
    (E := SymmetricSquare ξ.ker) (F := F)).1
    (covectorRestriction S ξ) (covectorRestriction T ξ)
  have hupper := (best_phase_supremum_specification hdim T).2.2.1 ξ hξ
  have hn := covectorRestriction_norm_sub_le S T ξ
  rw [he] at h
  have hle := (abs_le.mp h).2
  linarith

theorem bestPhaseSupremum_lipschitz
    (hdim : 2 ≤ Module.finrank ℝ V) :
    LipschitzWith 1 (bestPhaseSupremum (E := V) (F := F)) := by
  apply LipschitzWith.of_dist_le_mul
  intro S T
  have hST := bestPhaseSupremum_sub_le hdim S T
  have hTS := bestPhaseSupremum_sub_le hdim T S
  rw [norm_sub_rev] at hTS
  have h : |bestPhaseSupremum S - bestPhaseSupremum T| ≤ ‖S - T‖ :=
    abs_le.mpr ⟨by linarith, hST⟩
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using h

theorem bounded_phase_operator_set_compact [FiniteDimensional ℝ F]
    (hdim : 2 ≤ Module.finrank ℝ V) (R m : ℝ) :
    IsCompact {S : SymmetricSquare V →L[ℝ] F |
      ‖S‖ ≤ R ∧ m ≤ bestPhaseSupremum S} := by
  have hc : IsClosed {S : SymmetricSquare V →L[ℝ] F | m ≤ bestPhaseSupremum S} :=
    isClosed_le continuous_const (bestPhaseSupremum_lipschitz (F := F) hdim).continuous
  have he : {S : SymmetricSquare V →L[ℝ] F | ‖S‖ ≤ R ∧ m ≤ bestPhaseSupremum S} =
      Metric.closedBall 0 R ∩ {S | m ≤ bestPhaseSupremum S} := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
  rw [he]
  exact (isCompact_closedBall (0 : SymmetricSquare V →L[ℝ] F) R).inter_right hc

theorem actual_good_covector_of_positive_bestPhaseSupremum
    (hdim : 2 ≤ Module.finrank ℝ V) (S : SymmetricSquare V →L[ℝ] F)
    (hpos : 0 < bestPhaseSupremum S) :
    ∃ ξ : V →L[ℝ] ℝ, ‖ξ‖ = 1 ∧
      LinearSecondFormGoodCovector S.toLinearMap ξ.toLinearMap := by
  obtain ⟨ξ, hξ, he⟩ := best_phase_maximum_attainment hdim S
  let : Nontrivial ξ.ker := covector_kernel_nontrivial hdim ξ
  let : Nontrivial (SymmetricSquare ξ.ker) := symmetric_square_nontrivial
  have hξ0 : ξ ≠ 0 := by intro hz; rw [hz, norm_zero] at hξ; norm_num at hξ
  refine ⟨ξ, hξ, (linearSecondFormGoodCovector_iff_native_restriction S ξ).mpr ⟨hξ0, ?_⟩⟩
  exact (least_singular_norm_attainment (E := SymmetricSquare ξ.ker) (F := F)
    (covectorRestriction S ξ)).2.2.mp (by rwa [he])

#print axioms covectorRestriction_norm_sub_le
#print axioms bestPhaseSupremum_lipschitz
#print axioms bounded_phase_operator_set_compact
#print axioms actual_good_covector_of_positive_bestPhaseSupremum

end GlobalEmbedding.Offline
