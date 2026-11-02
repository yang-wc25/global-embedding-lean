import GlobalEmbedding.Offline.FiniteInjectiveMargins
import GlobalEmbedding.Paper.GoodCovectorNormedCriterion
import GlobalEmbedding.Paper.SupportedLocusLocalEquations

/-!
# Local quantitative reserves for an actual good dictionary

The restriction domains are the original symmetric squares of the actual covector
kernels, with the repository's canonical Hilbert quotient norms.  Starting only
from actual goodness at the reference operator, a finite dictionary has one positive
lower margin and one finite range-inverse bound throughout an open neighborhood.
No desired margin, alternate kernel, or independent second-form matrix is assumed.
-/

open GlobalEmbedding.Paper
open scoped Topology TensorProduct

namespace GlobalEmbedding.Offline

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance dictionarySquareRelationsClosed {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    IsClosed (symmetricSquareRelations V : Set (V ⊗[ℝ] V)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance dictionarySquareNormed {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    NormedAddCommGroup (SymmetricSquare V) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations V)

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem linearSecondFormGoodCovector_iff_native_restriction
    (B : SymmetricSquare V →L[ℝ] F) (ξ : V →L[ℝ] ℝ) :
    LinearSecondFormGoodCovector B.toLinearMap ξ.toLinearMap ↔
      ξ ≠ 0 ∧ Function.Injective (covectorRestriction B ξ) := by
  unfold LinearSecondFormGoodCovector
  have hmap := symmetric_square_linear_map_eq (E := ξ.ker) (F := V) ξ.ker.subtypeL
  change symmetricSquareLinearMap ξ.ker.subtype = symmetricSquareMap ξ.ker.subtypeL at hmap
  rw [hmap]
  have hn : ξ.toLinearMap ≠ 0 ↔ ξ ≠ 0 := by
    constructor
    · intro h hz
      exact h (by rw [hz]; rfl)
    · intro h hz
      exact h (ContinuousLinearMap.coe_injective hz)
  have hf : ((B.toLinearMap.comp (symmetricSquareMap ξ.ker.subtypeL)) :
      SymmetricSquare ξ.ker → F) = covectorRestriction B ξ := by
    funext z
    simp only [covectorRestriction, ContinuousLinearMap.comp_apply, LinearMap.comp_apply,
      symmetricSquareMapL_apply]
    rfl
  rw [hn, hf]

theorem actual_good_dictionary_local_reserves
    {ι : Type*} [Fintype ι]
    (B0 : SymmetricSquare V →L[ℝ] F) (ξ : ι → V →L[ℝ] ℝ)
    (hgood : ∀ i, LinearSecondFormGoodCovector B0.toLinearMap (ξ i).toLinearMap) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ U : Set (SymmetricSquare V →L[ℝ] F),
      IsOpen U ∧ B0 ∈ U ∧ ∀ B ∈ U, ∀ i,
        LinearSecondFormGoodCovector B.toLinearMap (ξ i).toLinearMap ∧
        (∀ z, μ * ‖z‖ ≤ ‖covectorRestriction B (ξ i) z‖) ∧
        ∃ e : SymmetricSquare (ξ i).ker ≃L[ℝ]
            LinearMap.range (covectorRestriction B (ξ i)).toLinearMap,
          (∀ z, (e z).val = covectorRestriction B (ξ i) z) ∧
          ‖e.symm.toContinuousLinearMap‖ ≤ μ⁻¹ := by
  let A : (SymmetricSquare V →L[ℝ] F) →
      ∀ i, SymmetricSquare (ξ i).ker →L[ℝ] F :=
    fun B i ↦ covectorRestriction B (ξ i)
  have hA (i : ι) : ContinuousAt (fun B ↦ A B i) B0 := by
    exact (continuous_id.clm_comp continuous_const).continuousAt
  have hi (i : ι) : Function.Injective (A B0 i) :=
    ((linearSecondFormGoodCovector_iff_native_restriction B0 (ξ i)).mp (hgood i)).2
  obtain ⟨μ, hμ, U, hU, hB0, hbound⟩ :=
    finite_injective_family_local_lower_bound
      (E := fun i : ι ↦ SymmetricSquare (ξ i).ker) (F := F) A B0 hA hi
  refine ⟨μ, hμ, U, hU, hB0, ?_⟩
  intro B hB i
  have hbi := hbound B hB i
  have hξ : ξ i ≠ 0 :=
    ((linearSecondFormGoodCovector_iff_native_restriction B0 (ξ i)).mp (hgood i)).1
  have hBinj : Function.Injective (covectorRestriction B (ξ i)) :=
    injective_of_positive_operator_lower_bound
      (E := SymmetricSquare (ξ i).ker) (F := F) (covectorRestriction B (ξ i)) hμ hbi
  refine ⟨(linearSecondFormGoodCovector_iff_native_restriction B (ξ i)).mpr
    ⟨hξ, hBinj⟩, hbi, ?_⟩
  exact inverse_range_norm_le_of_lower_bound
    (E := SymmetricSquare (ξ i).ker) (F := F) (covectorRestriction B (ξ i)) hμ hbi

#print axioms linearSecondFormGoodCovector_iff_native_restriction
#print axioms actual_good_dictionary_local_reserves

end GlobalEmbedding.Offline
