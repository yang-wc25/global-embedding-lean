import GlobalEmbedding.Offline.GoodRankOneDictionary
import GlobalEmbedding.Offline.GoodDictionaryMargins

/-!
# One actual good dictionary with operator and tensor reserves

Source: `main.tex` 690–696 and the full local conclusion of
`repair-good-rank-one-dictionary`.  One phase-regular second form and one positive
tensor produce the same finite good covectors, actual rank-one basis, continuous
coefficient map, positive coefficient neighborhood, and genuine kernel restriction
inverse bounds.  The symmetric-square norms and kernels are the original ones.

The operator neighborhood is in the actual fixed-target second-form space.  A
manifold two-jet must still be mapped into this neighborhood through its actual
projected second form; this theorem does not replace that geometric interface.
-/

noncomputable section

open GlobalEmbedding.Paper
open scoped TensorProduct ContDiff Topology

namespace GlobalEmbedding.Offline

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance reserveSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance reserveSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

-- These are exactly the existing native operator norms, cached for elaboration.
private noncomputable local instance reserveBilinearSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

private noncomputable local instance reserveBilinearNormed :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance reserveBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Complete local operator/tensor reserves for the same actual good dictionary.
Only a genuine phase witness and a positive definite source tensor are inputs.
In particular neither a dictionary, lower margin, basis inverse bound, open
neighborhood, positive coefficient reserve, nor smooth amplitudes are assumed.
-/
theorem positive_good_dictionary_with_operator_tensor_reserves
    (B0 : SymmetricSquare E →L[ℝ] F)
    (hphase : ∃ ξ : E →L[ℝ] ℝ,
      LinearSecondFormGoodCovector B0.toLinearMap ξ.toLinearMap)
    (g0 : E →L[ℝ] E →L[ℝ] ℝ)
    (hgsymm : ∀ v w, g0 v w = g0 w v)
    (hgpos : ∀ v, v ≠ 0 → 0 < g0 v v) :
    ∃ (ξ : EdgePair (Module.finrank ℝ E + 1) → E →L[ℝ] ℝ)
      (D : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ]
        (EdgePair (Module.finrank ℝ E + 1) → ℝ))
      (μ c L : ℝ)
      (U : Set (SymmetricSquare E →L[ℝ] F))
      (V : Set (E →L[ℝ] E →L[ℝ] ℝ)),
      0 < μ ∧ 0 < c ∧ 0 < L ∧
      IsOpen U ∧ B0 ∈ U ∧ IsOpen V ∧ g0 ∈ V ∧
      Fintype.card (EdgePair (Module.finrank ℝ E + 1)) =
        Module.finrank ℝ E * (Module.finrank ℝ E + 1) / 2 ∧
      (∀ i, ξ i ≠ 0) ∧
      LinearIndependent ℝ (fun i ↦ (ξ i).smulRight (ξ i)) ∧
      (∀ a, D (continuousRankOneReconstruct ξ a) = a) ∧
      (∀ A, (∀ v w, A v w = A w v) → continuousRankOneReconstruct ξ (D A) = A) ∧
      ‖D‖ ≤ L ∧ (∀ A, ‖D A‖ ≤ L * ‖A‖) ∧
      (∀ B ∈ U, ∀ i,
        LinearSecondFormGoodCovector B.toLinearMap (ξ i).toLinearMap ∧
        (∀ z, μ * ‖z‖ ≤ ‖covectorRestriction B (ξ i) z‖) ∧
        ∃ e : SymmetricSquare (ξ i).ker ≃L[ℝ]
            LinearMap.range (covectorRestriction B (ξ i)).toLinearMap,
          (∀ z, (e z).val = covectorRestriction B (ξ i) z) ∧
          ‖e.symm.toContinuousLinearMap‖ ≤ μ⁻¹) ∧
      (∀ A ∈ V, ∀ i, c ≤ D A i) ∧
      (∀ i, ContDiffOn ℝ ∞ (fun A ↦ Real.sqrt (D A i)) V) ∧
      (∀ A ∈ V, (∀ v w, A v w = A w v) →
        continuousRankOneReconstruct ξ (fun i ↦ (Real.sqrt (D A i)) ^ 2) = A) := by
  classical
  obtain ⟨ξ, D, hξ, hpositive, hleft, hright, hLI, hcard⟩ :=
    positive_good_rank_one_basis B0.toLinearMap hphase g0 hgsymm hgpos
  obtain ⟨μ, hμ, U, hU, hBU, hoperator⟩ :=
    actual_good_dictionary_local_reserves B0 ξ hξ
  obtain ⟨c, hc, V, hV, hgV, hcoeff⟩ :=
    coefficient_common_positive_neighborhood D g0 hpositive
  have hamplitude := dictionary_positive_square_root_amplitudes ξ D hright hc hcoeff
  let L := 1 + ‖D‖
  have hL : 0 < L := by
    dsimp [L]
    linarith [ContinuousLinearMap.opNorm_nonneg D]
  have hDL : ‖D‖ ≤ L := by dsimp [L]; linarith
  refine ⟨ξ, D, μ, c, L, U, V, hμ, hc, hL, hU, hBU, hV, hgV, hcard,
    ?_, hLI, hleft, hright, hDL, ?_, hoperator, hcoeff, hamplitude.1, hamplitude.2⟩
  · intro i
    exact ((linearSecondFormGoodCovector_iff_native_restriction B0 (ξ i)).mp (hξ i)).1
  · intro A
    exact (D.le_opNorm A).trans (mul_le_mul_of_nonneg_right hDL (norm_nonneg A))

#print axioms positive_good_dictionary_with_operator_tensor_reserves

end GlobalEmbedding.Offline
