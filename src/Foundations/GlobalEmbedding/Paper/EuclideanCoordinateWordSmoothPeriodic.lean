import GlobalEmbedding.Paper.EuclideanCoordinateWordTranslation
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Every actual finite coordinate-word derivative of a smooth integer-periodic lift
is smooth with the same periods. Inductively differentiate and evaluate at the actual
coordinate direction for smoothness; the genuine word translation identity and original
periodicity give the same integer periods. No restriction on word length is imposed.
Source: smooth derivatives in `literature/parallelizable-stable-plus-one/main.tex`,
proof of `lem:balanced`. -/
theorem euclideanCoordinateWordDerivative_smooth_periodic {a N : ℕ}
    (word : List (Fin a))
    (f : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hf : ContDiff ℝ ∞ f)
    (hp : ∀ x (m : Fin a → ℤ), f (x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) = f x) :
    ContDiff ℝ ∞ (euclideanCoordinateWordDerivative word f) ∧
      ∀ x (m : Fin a → ℤ),
        euclideanCoordinateWordDerivative word f
          (x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) =
        euclideanCoordinateWordDerivative word f x := by
  constructor
  · induction word with
    | nil => exact hf
    | cons i word ih =>
        exact (ih.fderiv_right (by simp)).clm_apply contDiff_const
  · intro x m
    have heq : (fun y ↦ f (y + WithLp.toLp 2 (fun i ↦ (m i : ℝ)))) = f :=
      funext (fun y ↦ hp y m)
    simpa only [heq] using
      (euclideanCoordinateWordDerivative_translate word f
        (WithLp.toLp 2 (fun i ↦ (m i : ℝ))) x).symm

#print axioms euclideanCoordinateWordDerivative_smooth_periodic

end GlobalEmbedding.Paper
