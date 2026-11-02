import GlobalEmbedding.Paper.IncrementsSymmetricCoordinateProducts
import GlobalEmbedding.Paper.SymmetricSquareTransportLowerBound
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# A fixed quantitative comparison for the original once-sorted coordinates

The source is exactly the native Euclidean data space of the original beta.
The target is the existing binary symmetric quotient with its canonical
Hilbert tensor quotient norm. The comparison constant depends on m alone,
and no alternative symmetric product or normalization is introduced.
-/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped TensorProduct BigOperators
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance actualIncrementSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance actualIncrementSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

def actualIncrementSortedSymmetricLinear (m : ℕ) :
    EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2} →ₗ[ℝ]
      SymmetricSquare (EuclideanSpace ℝ (Fin m)) :=
  ∑ q : {p : Fin m × Fin m // p.1 ≤ p.2},
    (EuclideanSpace.proj q).toLinearMap.smulRight
      (symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace.single q.val.1 1) (EuclideanSpace.single q.val.2 1))

theorem actualIncrementSortedSymmetricLinear_apply (m : ℕ)
    (t : EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2}) :
    actualIncrementSortedSymmetricLinear m t =
      ∑ q : {p : Fin m × Fin m // p.1 ≤ p.2}, t q •
        symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace.single q.val.1 1) (EuclideanSpace.single q.val.2 1) := by
  simp [actualIncrementSortedSymmetricLinear]

theorem actualIncrementSortedSymmetricLinear_injective (m : ℕ) :
    Function.Injective (actualIncrementSortedSymmetricLinear m) := by
  intro t u h
  have hs : (∑ q : {p : Fin m × Fin m // p.1 ≤ p.2}, (t q - u q) •
      symmetricSquareProduct (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace.single q.val.1 1) (EuclideanSpace.single q.val.2 1)) = 0 := by
    have hh := sub_eq_zero.mpr h
    simpa [actualIncrementSortedSymmetricLinear_apply, sub_smul,
      Finset.sum_sub_distrib] using hh
  have hli := Fintype.linearIndependent_iff.mp
    (increments_symmetric_coordinate_products_linearIndependent m)
  ext q
  exact sub_eq_zero.mp (hli (fun q => t q - u q) hs q)

def actualIncrementSortedSymmetricLeftInverse (m : ℕ) :
    SymmetricSquare (EuclideanSpace ℝ (Fin m)) →L[ℝ]
      EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2} :=
  (actualIncrementSortedSymmetricLinear m).leftInverse.toContinuousLinearMap

def actualIncrementSortedSymmetricConstant (m : ℕ) : ℝ :=
  1 + ‖actualIncrementSortedSymmetricLeftInverse m‖

theorem actualIncrementSortedSymmetricConstant_pos (m : ℕ) :
    0 < actualIncrementSortedSymmetricConstant m := by
  unfold actualIncrementSortedSymmetricConstant
  positivity

/-- The actual once-sorted coordinate vector is bounded by its canonical
symmetric tensor with a positive dimension-only constant, including m=0. -/
theorem actualIncrementSortedSymmetricLinear_lower (m : ℕ)
    (t : EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2}) :
    ‖t‖ ≤ actualIncrementSortedSymmetricConstant m *
      ‖actualIncrementSortedSymmetricLinear m t‖ := by
  have he : actualIncrementSortedSymmetricLeftInverse m
      (actualIncrementSortedSymmetricLinear m t) = t :=
    LinearMap.leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.mpr (actualIncrementSortedSymmetricLinear_injective m)) t
  calc
    ‖t‖ = ‖actualIncrementSortedSymmetricLeftInverse m
      (actualIncrementSortedSymmetricLinear m t)‖ := congrArg norm he.symm
    _ ≤ ‖actualIncrementSortedSymmetricLeftInverse m‖ *
      ‖actualIncrementSortedSymmetricLinear m t‖ :=
        (actualIncrementSortedSymmetricLeftInverse m).le_opNorm _
    _ ≤ actualIncrementSortedSymmetricConstant m *
      ‖actualIncrementSortedSymmetricLinear m t‖ :=
        mul_le_mul_of_nonneg_right (by
          unfold actualIncrementSortedSymmetricConstant
          linarith) (norm_nonneg _)

/-- A genuine chosen-operator homogeneous margin and a genuine inverse-chart
norm bound give a squared reserve on the same sorted coordinate space.
The only coordinate loss is the fixed canonical quotient comparison above. -/
theorem actual_increment_sorted_transport_reserve
    {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (m : ℕ) (e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] E)
    (S : SymmetricSquare E →L[ℝ] W) (eta C : ℝ)
    (heta : 0 ≤ eta) (hC : 0 < C)
    (hinv : ‖e.symm.toContinuousLinearMap‖^2 ≤ C)
    (hmargin : ∀ w, eta * ‖w‖ ≤ ‖S w‖)
    (t : EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2}) :
    (eta / (C * actualIncrementSortedSymmetricConstant m))^2 * ‖t‖^2 ≤
      ‖S (symmetricSquareMap e.toContinuousLinearMap
        (actualIncrementSortedSymmetricLinear m t))‖^2 := by
  have hK := actualIncrementSortedSymmetricConstant_pos m
  have ht := actualIncrementSortedSymmetricLinear_lower m t
  have hb := symmetricSquare_transport_lower_bound e S.toLinearMap eta C heta hC hinv
    hmargin (actualIncrementSortedSymmetricLinear m t)
  change (eta / C) * ‖actualIncrementSortedSymmetricLinear m t‖ ≤
    ‖S (symmetricSquareMap e.toContinuousLinearMap
      (actualIncrementSortedSymmetricLinear m t))‖ at hb
  have hfirst : (eta / (C * actualIncrementSortedSymmetricConstant m)) * ‖t‖ ≤
      (eta / C) * ‖actualIncrementSortedSymmetricLinear m t‖ := by
    calc
      _ = (eta / C) * (‖t‖ / actualIncrementSortedSymmetricConstant m) := by ring
      _ ≤ (eta / C) * ‖actualIncrementSortedSymmetricLinear m t‖ :=
        mul_le_mul_of_nonneg_left ((div_le_iff₀ hK).mpr (by
          simpa [mul_comm] using ht)) (div_nonneg heta hC.le)
  have hlow := hfirst.trans hb
  have hn : 0 ≤ (eta / (C * actualIncrementSortedSymmetricConstant m)) * ‖t‖ :=
    mul_nonneg (div_nonneg heta (mul_pos hC hK).le) (norm_nonneg t)
  have hsq := mul_self_le_mul_self hn hlow
  convert hsq using 1 <;> ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualIncrementSortedSymmetricLinear_lower
#print axioms GlobalEmbedding.Continuation.actual_increment_sorted_transport_reserve
