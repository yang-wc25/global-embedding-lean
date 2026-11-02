import GlobalEmbedding.Offline.JointGoodCovectorOpen
import GlobalEmbedding.Paper.SymmetricSquareSubspaceIsometry

/-!
# Quantitative joint good-covector neighborhoods on the actual moving kernels

The fixed-domain operator is the existing actual pair `(B, cξ)`. Its native
positive lower bound restricts to the literal original `Sym²(ker ξ)`: the
canonical inclusion is isometric and the actual contraction vanishes there.
This gives one positive restriction margin, and the reciprocal native range
inverse bound, for every actual covector in a common ball and every actual
second form in a common neighborhood. No varying-kernel identification or
surrogate restriction operator is introduced.
-/

noncomputable section
open GlobalEmbedding.Paper Set
open scoped TensorProduct Topology

namespace GlobalEmbedding.Offline

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance jointReserveRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance jointReserveSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The SAME actual pair on the native inclusion of the moving kernel has
exactly zero contraction component. -/
theorem secondFormContractionPair_on_covector_kernel
    (B : SymmetricSquare E →L[ℝ] F) (ξ : E →L[ℝ] ℝ)
    (z : SymmetricSquare ξ.ker) :
    secondFormContractionPair B ξ (symmetricSquareMapL ξ.ker.subtypeL z) =
      (covectorRestriction B ξ z, 0) := by
  have hz := congrArg (fun L : SymmetricSquare ξ.ker →ₗ[ℝ] E ↦ L z)
    (contractionKernel_comp_inclusion_eq_zero ξ.toLinearMap)
  have hmap := symmetric_square_linear_map_eq (E := ξ.ker) (F := E) ξ.ker.subtypeL
  change symmetricSquareLinearMap ξ.ker.subtype = symmetricSquareMap ξ.ker.subtypeL at hmap
  change contractionKernelQuotientMap ξ.toLinearMap
    (symmetricSquareLinearMap ξ.ker.subtype z) = 0 at hz
  rw [hmap] at hz
  apply Prod.ext
  · rfl
  · change contractionKernelQuotientMap ξ.toLinearMap
      (symmetricSquareMapL ξ.ker.subtypeL z) = 0
    simpa only [symmetricSquareMapL_apply] using hz

/-- A lower bound on the existing fixed-domain pair restricts with NO loss
to the actual canonical norm on the literal moving `Sym²(ker ξ)`. -/
theorem covectorRestriction_lower_bound_of_contraction_pair
    (B : SymmetricSquare E →L[ℝ] F) (ξ : E →L[ℝ] ℝ) (μ : ℝ)
    (hbound : ∀ q, μ * ‖q‖ ≤ ‖secondFormContractionPair B ξ q‖) :
    ∀ z, μ * ‖z‖ ≤ ‖covectorRestriction B ξ z‖ := by
  intro z
  have h := hbound (symmetricSquareMapL ξ.ker.subtypeL z)
  rw [symmetric_square_subspace_isometry ξ.ker z,
    secondFormContractionPair_on_covector_kernel B ξ z] at h
  simpa only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)] using h

/-- Starting only from one ORIGINAL good pair, the same positive margin and
native inverse bound hold for every moving actual covector in one ball and
every actual second form in one neighborhood. The reference covector may have
arbitrary nonzero norm, and no nontriviality of its kernel is assumed. -/
theorem actual_good_covector_product_ball_reserves
    (B0 : SymmetricSquare E →L[ℝ] F) (ξ0 : E →L[ℝ] ℝ)
    (hgood : LinearSecondFormGoodCovector B0.toLinearMap ξ0.toLinearMap) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ U : Set (SymmetricSquare E →L[ℝ] F), IsOpen U ∧ B0 ∈ U ∧
        ∀ B ∈ U, ∀ ξ : E →L[ℝ] ℝ, ‖ξ - ξ0‖ < ε →
          LinearSecondFormGoodCovector B.toLinearMap ξ.toLinearMap ∧
          (∀ z, μ * ‖z‖ ≤ ‖covectorRestriction B ξ z‖) ∧
          ∃ e : SymmetricSquare ξ.ker ≃L[ℝ]
              LinearMap.range (covectorRestriction B ξ).toLinearMap,
            (∀ z, (e z).val = covectorRestriction B ξ z) ∧
            ‖e.symm.toContinuousLinearMap‖ ≤ μ⁻¹ := by
  let P := (SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] ℝ)
  let A : P → ∀ _ : Unit, SymmetricSquare E →L[ℝ] F × E :=
    fun p _ ↦ secondFormContractionPair p.1 p.2
  have hA (_ : Unit) : ContinuousAt (fun p ↦ A p ()) (B0, ξ0) :=
    continuous_secondFormContractionPair.continuousAt
  have hinj (_ : Unit) : Function.Injective (A (B0, ξ0) ()) :=
    ((good_iff_secondFormContractionPair_injective B0 ξ0).mp hgood).2
  obtain ⟨μ, hμ, V, hV, hp0, hbound⟩ := finite_injective_family_local_lower_bound
    (E := fun _ : Unit ↦ SymmetricSquare E) (F := F × E) A (B0, ξ0) hA hinj
  let W : Set P := V ∩ {p | p.2 ≠ 0}
  have hW : IsOpen W := hV.inter (isOpen_ne.preimage continuous_snd)
  have hpW : (B0, ξ0) ∈ W :=
    ⟨hp0, ((good_iff_secondFormContractionPair_injective B0 ξ0).mp hgood).1⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW (B0, ξ0) hpW
  refine ⟨μ, hμ, ε, hε, Metric.ball B0 ε, Metric.isOpen_ball,
    Metric.mem_ball_self hε, ?_⟩
  intro B hB ξ hξ
  have hpball : (B, ξ) ∈ Metric.ball (B0, ξ0) ε := by
    change max (dist B B0) (dist ξ ξ0) < ε
    exact max_lt hB (by simpa only [dist_eq_norm] using hξ)
  have hp := hball hpball
  have hlow : ∀ z, μ * ‖z‖ ≤ ‖covectorRestriction B ξ z‖ :=
    covectorRestriction_lower_bound_of_contraction_pair B ξ μ (hbound (B, ξ) hp.1 ())
  have hnative := injective_of_positive_operator_lower_bound
    (E := SymmetricSquare ξ.ker) (F := F) (covectorRestriction B ξ) hμ hlow
  exact ⟨(linearSecondFormGoodCovector_iff_native_restriction B ξ).mpr ⟨hp.2, hnative⟩,
    hlow, inverse_range_norm_le_of_lower_bound
      (E := SymmetricSquare ξ.ker) (F := F) (covectorRestriction B ξ) hμ hlow⟩

#print axioms secondFormContractionPair_on_covector_kernel
#print axioms covectorRestriction_lower_bound_of_contraction_pair
#print axioms actual_good_covector_product_ball_reserves

end GlobalEmbedding.Offline
