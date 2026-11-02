import GlobalEmbedding.Paper.LittlePeriodicCAlphaSpace
import GlobalEmbedding.Paper.PeriodicCAlphaValueBound

/-!
# Bounded evaluation on the actual little periodic Hölder space

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Evaluation at a fixed real orbit point is continuous for the little
Hölder norm. This module proves that fact for the actual periodic norm and closure subtype.
-/

namespace GlobalEmbedding.Paper

/-- Evaluation at any point of the Euclidean lift is a real continuous linear map on the actual
little periodic Hölder space, with operator norm at most one.

Source: Proposition `prop:collar`, proof lines 530–534, evaluation of the translated fixed point.
The little space inherits the actual periodic Hölder vector operations and norm from its closure
submodule. Its pointwise operation laws make evaluation linear. The proved global value bound
`‖f(y)‖≤periodicCAlphaNorm(f)` is exactly `‖ev_y(f)‖≤‖f‖` for this norm. LinearMap.mkContinuous
therefore constructs the evaluation CLM, and its norm bound gives operator norm at most one.
This requires no completeness assumption and includes zero domain or target dimension.
-/
theorem collar_little_holder_evaluation
    {a N k : ℕ} {α : ℝ} (y : EuclideanSpace ℝ (Fin a)) :
    ∃ ev : LittlePeriodicCAlphaFunction a N k α →L[ℝ] EuclideanSpace ℝ (Fin N),
      (∀ f : LittlePeriodicCAlphaFunction a N k α,
        ev f = (f : PeriodicCAlphaFunction a N k α).toFun y) ∧ ‖ev‖ ≤ 1 := by
  let L : LittlePeriodicCAlphaFunction a N k α →ₗ[ℝ] EuclideanSpace ℝ (Fin N) :=
    { toFun := fun f ↦ (f : PeriodicCAlphaFunction a N k α).toFun y
      map_add' := by
        intro f g
        change ((f : PeriodicCAlphaFunction a N k α) +
          (g : PeriodicCAlphaFunction a N k α)).toFun y = _
        exact congrArg (fun h ↦ h y)
          ((periodicCAlpha_pointwise_operations a N k α).2.1 _ _)
      map_smul' := by
        intro c f
        change (c • (f : PeriodicCAlphaFunction a N k α)).toFun y = _
        exact congrArg (fun h ↦ h y)
          ((periodicCAlpha_pointwise_operations a N k α).2.2 c _) }
  have hbound (f : LittlePeriodicCAlphaFunction a N k α) : ‖L f‖ ≤ 1 * ‖f‖ := by
    change ‖(f : PeriodicCAlphaFunction a N k α).toFun y‖ ≤ 1 *
      periodicCAlphaNorm (f : PeriodicCAlphaFunction a N k α)
    simpa only [one_mul] using periodicCAlpha_value_bound
      (f : PeriodicCAlphaFunction a N k α) y
  refine ⟨L.mkContinuous 1 hbound, fun f ↦ rfl, ?_⟩
  exact L.mkContinuous_norm_le zero_le_one hbound

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_little_holder_evaluation
