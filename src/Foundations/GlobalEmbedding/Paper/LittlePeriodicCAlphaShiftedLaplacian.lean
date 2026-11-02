import GlobalEmbedding.Paper.LittlePeriodicCAlphaDirectionalDerivative
import GlobalEmbedding.Paper.LittlePeriodicCAlphaRestrictOrder

/-!
# The original shifted Laplacian on the actual little periodic spaces

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 384.
DAG node: `balanced-inverse-periodic-laplacian`.
-/

namespace GlobalEmbedding.Paper

/-- The period-one operator Σ_i D_i²−1, as an actual bounded real linear map from the
original little C^{2,α} closure to its original little C^{0,α} closure.

Compose the already proved actual directional derivatives in each Euclidean coordinate
basis direction, sum the finitely many continuous linear maps, and subtract the actual
regularity inclusion. Every summand preserves the true smooth closure by its construction;
no PDE solvability is used. For a=0 the sum is empty, so this is minus the inclusion.
Source: `lem:balanced`, proof line 384. -/
noncomputable def littlePeriodicCAlphaShiftedLaplacian {a N : ℕ} {α : ℝ}
    (hα : α ≤ 1) :
    LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a N 0 α :=
  (∑ i : Fin a,
    (littlePeriodicCAlphaDirectionalDerivative (N := N) (k := 0) (α := α)
      (EuclideanSpace.basisFun (Fin a) ℝ i)).comp
    (littlePeriodicCAlphaDirectionalDerivative (N := N) (k := 1) (α := α)
      (EuclideanSpace.basisFun (Fin a) ℝ i))) -
    littlePeriodicCAlphaRestrictOrder 0 (by omega) hα

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.littlePeriodicCAlphaShiftedLaplacian
