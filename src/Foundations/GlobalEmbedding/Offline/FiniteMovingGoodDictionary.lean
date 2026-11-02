import GlobalEmbedding.Offline.JointGoodCovectorReserves
import GlobalEmbedding.Offline.CompactGoodDictionaryTemplates

/-!
# Common actual moving-kernel reserves for a fixed finite good dictionary

Each reference covector is good for the SAME actual second form `B0`. The
already proved joint ball reserves yield one common positive covector radius,
one common positive canonical restriction margin, and one common open operator
neighborhood. All conclusions concern each literal moving `Sym²(ker η)` and
its actual range inverse. The finite positive minimum inserts the value one,
so the empty dictionary requires no nonempty-index hypothesis.

The constants belong to this fixed finite family. No independence of the
family or geometric chart data, and no covector transport between charts, is
claimed by this consumer.
-/

noncomputable section
open GlobalEmbedding.Paper Set
open scoped TensorProduct Topology

namespace GlobalEmbedding.Offline

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance movingDictionaryRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance movingDictionarySquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A fixed finite family of original good covectors admits common positive
reserves for every actual nearby second form and every moving covector in the
same-radius ball about any member. Empty families and zero-dimensional kernels
are included. -/
theorem finite_moving_good_dictionary_reserves
    {ι : Type*} [Finite ι]
    (B0 : SymmetricSquare E →L[ℝ] F) (ξ : ι → E →L[ℝ] ℝ)
    (hgood : ∀ i, LinearSecondFormGoodCovector B0.toLinearMap (ξ i).toLinearMap) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ U : Set (SymmetricSquare E →L[ℝ] F), IsOpen U ∧ B0 ∈ U ∧
        ∀ B ∈ U, ∀ i : ι, ∀ η : E →L[ℝ] ℝ, ‖η - ξ i‖ < ε →
          LinearSecondFormGoodCovector B.toLinearMap η.toLinearMap ∧
          (∀ z, μ * ‖z‖ ≤ ‖covectorRestriction B η z‖) ∧
          ∃ e : SymmetricSquare η.ker ≃L[ℝ]
              LinearMap.range (covectorRestriction B η).toLinearMap,
            (∀ z, (e z).val = covectorRestriction B η z) ∧
            ‖e.symm.toContinuousLinearMap‖ ≤ μ⁻¹ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hres := fun i ↦ actual_good_covector_product_ball_reserves B0 (ξ i) (hgood i)
  choose μi hμi εi hεi Ui hUi hB0 hcontrol using hres
  obtain ⟨μ, hμ, hμle⟩ := finite_positive_common_lower_bound μi hμi
  obtain ⟨ε, hε, hεle⟩ := finite_positive_common_lower_bound εi hεi
  refine ⟨μ, hμ, ε, hε, ⋂ i, Ui i, isOpen_iInter_of_finite hUi,
    Set.mem_iInter.mpr hB0, ?_⟩
  intro B hB i η hη
  obtain ⟨hg, hlower, e, he, hinv⟩ :=
    hcontrol i B (Set.mem_iInter.mp hB i) η (hη.trans_le (hεle i))
  refine ⟨hg, ?_, e, he, ?_⟩
  · intro z
    exact (mul_le_mul_of_nonneg_right (hμle i) (norm_nonneg z)).trans (hlower z)
  · exact hinv.trans ((inv_le_inv₀ (hμi i) hμ).mpr (hμle i))

#print axioms finite_moving_good_dictionary_reserves

end GlobalEmbedding.Offline
