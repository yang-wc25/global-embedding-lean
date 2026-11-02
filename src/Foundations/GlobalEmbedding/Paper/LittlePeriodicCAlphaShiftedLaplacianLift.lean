import GlobalEmbedding.Paper.LittlePeriodicCAlphaShiftedLaplacian
import GlobalEmbedding.Paper.CollarLittleHolderEvaluation

/-!
# Exact lift of the original shifted little Hölder Laplacian

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 384.
DAG node: `balanced-inverse-periodic-laplacian-lift`.
-/

namespace GlobalEmbedding.Paper

/-- The constructed bounded operator has exactly the original sum of actual second
coordinate derivatives minus the original lift.

Proof: use the proved continuous linear evaluation on the original little target space.
It commutes with the finite operator sum and subtraction. Each composed derivative has
its defining actual fderiv lift, while the actual regularity inclusion preserves the lift.
All dimensions, including empty coordinate or target types, are retained.
Source: `lem:balanced`, proof line 384. -/
theorem littlePeriodicCAlphaShiftedLaplacian_lift {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (u : LittlePeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    (littlePeriodicCAlphaShiftedLaplacian hα u).val.toFun x =
      (∑ i : Fin a, fderiv ℝ
        (fun y ↦ fderiv ℝ u.val.toFun y (EuclideanSpace.basisFun (Fin a) ℝ i)) x
        (EuclideanSpace.basisFun (Fin a) ℝ i)) - u.val.toFun x := by
  obtain ⟨ev, hev, _⟩ := collar_little_holder_evaluation
    (N := N) (k := 0) (α := α) x
  rw [← hev]
  unfold littlePeriodicCAlphaShiftedLaplacian
  rw [sub_apply, map_sub, sum_apply, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [hev]
    rfl
  · rw [hev]
    rfl

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.littlePeriodicCAlphaShiftedLaplacian_lift
