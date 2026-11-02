import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusTranslate
import GlobalEmbedding.Paper.PeriodicCAlphaTranslateLift

/-!
# Every-lift formula for the actual little Hölder torus translation

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-torus-translation-lift-formula`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- The constructed torus operator equals actual translation by every Euclidean lift.

Proof: its chosen representative has the prescribed torus projection. Raw lift independence
therefore identifies the operators on underlying lifts, and subtype extensionality gives
operator equality. Source: integer-periodic torus translation in `lem:balanced`. -/
theorem littlePeriodicCAlphaTorusTranslate_lift {a N k : ℕ} {α : ℝ}
    (h : EuclideanSpace ℝ (Fin a)) :
    littlePeriodicCAlphaTorusTranslate (N := N) (k := k) (α := α)
      (toLp 2 (fun i : Fin a ↦ (h i : AddCircle (1 : ℝ)))) =
      littlePeriodicCAlphaTranslateIsometry h := by
  apply LinearIsometry.ext
  intro f
  apply Subtype.ext
  exact periodicCAlphaTranslate_lift_independent _ h
    (periodic_flat_torus_projection.surjective
      (toLp 2 (fun i : Fin a ↦ (h i : AddCircle (1 : ℝ))))).choose_spec f.val

#print axioms littlePeriodicCAlphaTorusTranslate_lift

end GlobalEmbedding.Paper
