import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Actual ambient Euclidean ball volumes

A compact source can first be smoothly embedded in an auxiliary Euclidean
space. Applying the existing volume-packing proof in that ambient space avoids
introducing an unproved Riemannian-volume comparison assumption. The auxiliary
ambient dimension affects only the fixed number of colors, not the target
isometric-immersion dimension. Dimension zero is included.
-/

open Set Metric MeasureTheory
open scoped ENNReal

namespace GlobalEmbedding.Initialization

/-- The positive, finite coefficient is the actual volume of the unit ball.
The native Haar dilation theorem proves the exact volume formula at every
positive radius, so both bounds required by `VolumePacking` are supplied with
the same internally obtained constant. No volume estimate is assumed. -/
theorem exists_euclidean_ball_volume_coefficient (d : ℕ) :
    ∃ α : ℝ, 0 < α ∧ ∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      volume (eball x (ENNReal.ofReal r)) = ENNReal.ofReal (α * r ^ d) := by
  let E := EuclideanSpace ℝ (Fin d)
  let α : ℝ := (volume (ball (0 : E) 1)).toReal
  have hfinite : volume (ball (0 : E) 1) ≠ ⊤ := measure_ball_ne_top
  have hpos : 0 < α := ENNReal.toReal_pos
    (ne_of_gt (measure_ball_pos volume (0 : E) zero_lt_one)) hfinite
  have hα : ENNReal.ofReal α = volume (ball (0 : E) 1) :=
    ENNReal.ofReal_toReal hfinite
  refine ⟨α, hpos, ?_⟩
  intro x r hr
  rw [Metric.eball_ofReal, Measure.addHaar_ball_of_pos volume x hr,
    finrank_euclideanSpace, Fintype.card_fin, ← hα,
    ← ENNReal.ofReal_mul (pow_nonneg hr.le _)]
  congr 1
  ring

end GlobalEmbedding.Initialization
