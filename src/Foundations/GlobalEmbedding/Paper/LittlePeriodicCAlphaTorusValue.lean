import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusTranslate

/-!
# Actual values of a little Hölder function on the original flat torus

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-little-torus-value`.
-/

namespace GlobalEmbedding.Paper

/-- Evaluate an actual little Hölder function at an actual flat-torus point by actual
translation followed by evaluation at the original fiber origin.

This uses the already constructed actual torus action. The every-lift value formula is a
separate theorem, so this is genuine specified data with no assumed representative
independence or alternate quotient function. Source: recovery by evaluating translated
solutions at the fiber origin in the proof of `lem:balanced`. -/
noncomputable def littlePeriodicCAlphaTorusValue {a N k : ℕ} {α : ℝ}
    (f : LittlePeriodicCAlphaFunction a N k α)
    (q : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) : EuclideanSpace ℝ (Fin N) :=
  (littlePeriodicCAlphaTorusTranslate q f).val.toFun 0

#print axioms littlePeriodicCAlphaTorusValue

end GlobalEmbedding.Paper
