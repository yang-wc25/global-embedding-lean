import Probes.ActualIncrementSymmetricCoordinates
import GlobalEmbedding.Paper.IncrementsModeAmbientTransverseFrame
import GlobalEmbedding.Paper.TrueSecondFormL
import GlobalEmbedding.Paper.CovectorRestriction
import GlobalEmbedding.Paper.SymmetricSquareMapProduct
import GlobalEmbedding.Paper.LeastSingularNormBound

/-!
# Actual chosen-phase margins supply the original transverse-frame reserve

The operator is the original restricted true second form, with its canonical
quotient norm. The chart/kernel equivalence identifies the actual transverse
coordinate directions, and its inverse norm is retained. The resulting
reserve concerns the SAME original ambient beta-adjoint frame. A best-phase
maximum is never substituted for the margin of the phase actually chosen.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function Bundle
open scoped ContDiff TensorProduct BigOperators
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance chosenMarginSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance chosenMarginSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [RiemannianBundle (TangentSpace I : M → Type _)]
  {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "D0" => EuclideanSpace ℝ (Fin m)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

/-- The sorted columns of the original frame are the exact chart pullback
of the original covector restriction. This is an equality of the actual
operators and preserves the original quotient product normalization. -/
theorem actual_increment_frame_eq_chosen_restriction
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (x : D)
    (xi : TangentSpace I (c x) →L[ℝ] ℝ) (e : D0 ≃L[ℝ] xi.ker)
    (he : ∀ a : Fin m, ((e (EuclideanSpace.single a 1)) : TangentSpace I (c x)) =
      incrementsModeCoordinateDirections c x a.succ) (t : Tdata) :
    incrementsModeAmbientTransverseFrame F hF c x t =
      (covectorRestriction (trueSecondFormL F hF (c x)) xi
        (symmetricSquareMap e.toContinuousLinearMap
          (actualIncrementSortedSymmetricLinear m t)) : V) := by
  rw [← symmetricSquareMapL_apply, actualIncrementSortedSymmetricLinear_apply]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]
  unfold incrementsModeAmbientTransverseFrame
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  unfold covectorRestriction
  simp only [ContinuousLinearMap.comp_apply, symmetricSquareMapL_product]
  change (incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ : V) =
    (trueSecondForm F hF (c x) (symmetricSquareProduct (TangentSpace I (c x))
      ((e (EuclideanSpace.single q.val.1 1)) : TangentSpace I (c x))
      ((e (EuclideanSpace.single q.val.2 1)) : TangentSpace I (c x))) : V)
  rw [he, he]
  rfl

/-- The actual chosen margin and the chart inverse bound give the squared
reserve needed by the actual original transverse Gram inverse. -/
theorem actual_increment_frame_reserve_of_chosen_margin
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (x : D)
    (xi : TangentSpace I (c x) →L[ℝ] ℝ) (e : D0 ≃L[ℝ] xi.ker)
    (he : ∀ a : Fin m, ((e (EuclideanSpace.single a 1)) : TangentSpace I (c x)) =
      incrementsModeCoordinateDirections c x a.succ)
    (eta C : ℝ) (heta : 0 ≤ eta) (hC : 0 < C)
    (hinv : ‖e.symm.toContinuousLinearMap‖^2 ≤ C)
    (hmargin : ∀ w : SymmetricSquare xi.ker, eta * ‖w‖ ≤
      ‖covectorRestriction (trueSecondFormL F hF (c x)) xi w‖)
    (t : Tdata) :
    (eta / (C * actualIncrementSortedSymmetricConstant m))^2 * ‖t‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame F hF c x t‖^2 := by
  rw [actual_increment_frame_eq_chosen_restriction F hF c x xi e he t]
  exact actual_increment_sorted_transport_reserve m e
    (covectorRestriction (trueSecondFormL F hF (c x)) xi) eta C heta hC hinv hmargin t

/-- In a nontrivial actual phase kernel, a lower bound on the original
least singular norm is exactly the homogeneous margin used above. -/
theorem actual_increment_frame_reserve_of_leastSingular
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (x : D)
    (xi : TangentSpace I (c x) →L[ℝ] ℝ) (e : D0 ≃L[ℝ] xi.ker)
    [Nontrivial (SymmetricSquare xi.ker)]
    (he : ∀ a : Fin m, ((e (EuclideanSpace.single a 1)) : TangentSpace I (c x)) =
      incrementsModeCoordinateDirections c x a.succ)
    (eta C : ℝ) (heta : 0 ≤ eta) (hC : 0 < C)
    (hinv : ‖e.symm.toContinuousLinearMap‖^2 ≤ C)
    (hmargin : eta ≤ leastSingularNorm (E := SymmetricSquare xi.ker)
      (F := normalSpace (I := I) F (c x))
        (covectorRestriction (trueSecondFormL F hF (c x)) xi))
    (t : Tdata) :
    (eta / (C * actualIncrementSortedSymmetricConstant m))^2 * ‖t‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame F hF c x t‖^2 := by
  let S : SymmetricSquare xi.ker →L[ℝ] normalSpace (I := I) F (c x) :=
    covectorRestriction (trueSecondFormL F hF (c x)) xi
  have hs := least_singular_norm_bound (E := SymmetricSquare xi.ker)
    (F := normalSpace (I := I) F (c x)) S
  have hm : ∀ w : SymmetricSquare xi.ker, eta * ‖w‖ ≤ ‖S w‖ :=
    (hs.2.2 eta).mp hmargin
  exact actual_increment_frame_reserve_of_chosen_margin F hF c x xi e he eta C heta hC hinv hm t

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_frame_eq_chosen_restriction
#print axioms GlobalEmbedding.Continuation.actual_increment_frame_reserve_of_chosen_margin
#print axioms GlobalEmbedding.Continuation.actual_increment_frame_reserve_of_leastSingular
