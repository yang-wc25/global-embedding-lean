import GlobalEmbedding.Paper.LittlePeriodicCAlphaDirectionalDerivativeBound
import GlobalEmbedding.Paper.PeriodicCAlphaValueBound

/-!
# Actual little Hölder norm bounds for the vertical coordinate jets

Source: `main.tex`, `lem:balanced`, line418. This consumes the actual quotient periodic
value and directional derivative norm theorems. No substitute norm is introduced.
-/

open scoped ContDiff
namespace GlobalEmbedding.Paper

/-- Every actual value of the little-space lift is bounded by its original actual norm. -/
theorem littlePeriodicCAlpha_value_norm_le {a N k : ℕ} {α : ℝ}
    (f : LittlePeriodicCAlphaFunction a N k α) (x : EuclideanSpace ℝ (Fin a)) :
    ‖f.val.toFun x‖ ≤ ‖f‖ :=
  periodicCAlpha_value_bound f.val x

/-- Each first coordinate derivative of the actual little lift is bounded by the same norm. -/
theorem littlePeriodicCAlpha_first_coordinate_norm_le {a N k : ℕ} {α : ℝ}
    (f : LittlePeriodicCAlphaFunction a N (k + 1) α)
    (x : EuclideanSpace ℝ (Fin a)) (i : Fin a) :
    ‖fderiv ℝ f.val.toFun x (EuclideanSpace.single i (1 : ℝ))‖ ≤ ‖f‖ := by
  let e := EuclideanSpace.single i (1 : ℝ)
  calc
    _ ≤ ‖periodicCAlphaDirectionalDerivative e f.val‖ :=
      periodicCAlpha_value_bound (periodicCAlphaDirectionalDerivative e f.val) x
    _ ≤ ‖e‖ * ‖f.val‖ := periodicCAlphaDirectionalDerivative_norm e f.val
    _ = ‖f‖ := by simp [e]

/-- Each ordered second coordinate derivative of the actual little C² lift has the same bound. -/
theorem littlePeriodicCAlpha_second_coordinate_norm_le {a N : ℕ} {α : ℝ}
    (f : LittlePeriodicCAlphaFunction a N 2 α)
    (x : EuclideanSpace ℝ (Fin a)) (i j : Fin a) :
    ‖fderiv ℝ (fun y ↦ fderiv ℝ f.val.toFun y (EuclideanSpace.single j (1 : ℝ))) x
      (EuclideanSpace.single i (1 : ℝ))‖ ≤ ‖f‖ := by
  let ei := EuclideanSpace.single i (1 : ℝ)
  let ej := EuclideanSpace.single j (1 : ℝ)
  let g := periodicCAlphaDirectionalDerivative (k := 1) ej f.val
  calc
    _ ≤ ‖periodicCAlphaDirectionalDerivative ei g‖ :=
      periodicCAlpha_value_bound (periodicCAlphaDirectionalDerivative ei g) x
    _ ≤ ‖ei‖ * ‖g‖ := periodicCAlphaDirectionalDerivative_norm ei g
    _ ≤ ‖ei‖ * (‖ej‖ * ‖f.val‖) :=
      mul_le_mul_of_nonneg_left (periodicCAlphaDirectionalDerivative_norm ej f.val)
        (norm_nonneg ei)
    _ = ‖f‖ := by simp [ei, ej]

#print axioms littlePeriodicCAlpha_value_norm_le
#print axioms littlePeriodicCAlpha_first_coordinate_norm_le
#print axioms littlePeriodicCAlpha_second_coordinate_norm_le
end GlobalEmbedding.Paper
