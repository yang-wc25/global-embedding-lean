import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusValue
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusTranslateLift

/-!
# Every-lift formula for actual little Hölder values on the original torus

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-little-torus-value-lift`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- Actual torus evaluation agrees with the original lift at every actual representative.

Use the already proved every-lift formula for the actual torus action. Its value at zero is
the original lift at zero plus h, exactly the lift at h. Source: recovery of joint fiber
regularity at the end of the proof of `lem:balanced`. -/
theorem littlePeriodicCAlphaTorusValue_lift {a N k : ℕ} {α : ℝ}
    (f : LittlePeriodicCAlphaFunction a N k α) (h : EuclideanSpace ℝ (Fin a)) :
    littlePeriodicCAlphaTorusValue f
      (toLp 2 (fun i : Fin a ↦ (h i : AddCircle (1 : ℝ)))) = f.val.toFun h := by
  unfold littlePeriodicCAlphaTorusValue
  rw [littlePeriodicCAlphaTorusTranslate_lift]
  change f.val.toFun (0 + h) = f.val.toFun h
  rw [zero_add]

#print axioms littlePeriodicCAlphaTorusValue_lift

end GlobalEmbedding.Paper
