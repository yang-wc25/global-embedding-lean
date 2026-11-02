import GlobalEmbedding.Paper.CollarComplexHolderSpace
import GlobalEmbedding.Paper.PeriodicCAlphaValueBound

/-!
# Bounded complex evaluation on the actual complex little Hölder space

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Evaluation at a real orbit point is the actual complex linear map
needed to recover pointwise Taylor identities from complex little-space norm sums.
-/

namespace GlobalEmbedding.Paper

/-- Actual complex point evaluation is continuous and complex linear, with operator norm at
most one for the original Hölder norm.

Source: Proposition `prop:collar`, proof lines 530–534. Pointwise operation laws give complex
linearity. Orthogonal coordinates preserve the value norm, and the actual realified Hölder
norm bounds every value of its lift. This supplies the norm bound to construct the continuous
linear map and its operator-norm estimate. Includes zero domain and target dimensions.
-/
theorem collar_complex_holder_evaluation {a N k : ℕ} {α : ℝ}
    (y : EuclideanSpace ℝ (Fin a)) :
    ∃ ev : CollarComplexHolderSpace a N k α →L[ℂ] EuclideanSpace ℂ (Fin N),
      (∀ f, ev f = collarComplexHolderFunction f y) ∧ ‖ev‖ ≤ 1 := by
  let L : CollarComplexHolderSpace a N k α →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    { toFun := fun f ↦ collarComplexHolderFunction f y
      map_add' := fun f g ↦ congrFun (collarComplexHolderFunction_add f g) y
      map_smul' := fun c f ↦ congrFun (collarComplexHolderFunction_smul c f) y }
  have hbound (f : CollarComplexHolderSpace a N k α) : ‖L f‖ ≤ 1 * ‖f‖ := by
    change ‖(collarComplexHolderCoordinates N).symm (f.val.toFun y)‖ ≤ 1 * ‖f‖
    rw [LinearIsometryEquiv.norm_map, one_mul]
    exact periodicCAlpha_value_bound f.val y
  exact ⟨L.mkContinuous 1 hbound, fun _ ↦ rfl,
    L.mkContinuous_norm_le zero_le_one hbound⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_complex_holder_evaluation
