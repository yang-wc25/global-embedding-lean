import GlobalEmbedding.Paper.CollarHolderUniformAnalyticNeighborhood
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusValueLift
import GlobalEmbedding.Paper.PeriodicFlatTorusProductLiftOn
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Native joint analyticity of actual little Hölder values on the original torus

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. The actual original torus atlas is used with analytic order omega.
-/

open Set
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Actual joint analyticity of a real little Hölder lift along one full base fiber gives
native joint analytic regularity on one common actual base neighborhood times the original torus.

Source: Proposition `prop:collar`, proof lines 530–534. Actual periodic compactness first
constructs a common positive base neighborhood where the lift is analytic at every point.
An actual analytic map with Euclidean target is genuinely C^omega there. The proved every-lift
identity identifies this actual lift with actual torus evaluation, and the existing genuine
product lifting theorem descends that analytic-order regularity to the original torus atlas.
The order is omega, not the smooth order infinity. No torus value, chart, quotient regularity
or manifold-analyticity data are assumed or replaced, and no global instance is installed. -/
theorem collar_holder_native_joint_analytic
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {a N k : ℕ} {α : ℝ}
    (u : P → LittlePeriodicCAlphaFunction a N k α) (p₀ : P)
    (hu : ∀ y : EuclideanSpace ℝ (Fin a),
      AnalyticAt ℝ (fun z : P × EuclideanSpace ℝ (Fin a) ↦
        (u z.1).val.toFun z.2) (p₀, y)) :
    ∃ ε : ℝ, 0 < ε ∧
      let _charted := periodicFlatTorusChartedSpace a
      ContMDiffOn ((𝓘(ℝ, P)).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin a))))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin N))) ω
        (fun z : P × PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)) ↦
          littlePeriodicCAlphaTorusValue (u z.1) z.2) (Metric.ball p₀ ε ×ˢ univ) := by
  obtain ⟨ε, hε, ha⟩ := collar_holder_uniform_analytic_neighborhood u p₀ hu
  refine ⟨ε, hε, ?_⟩
  dsimp only
  let _charted := periodicFlatTorusChartedSpace a
  apply (periodic_flat_torus_product_lift_contMDiffOn_iff ω
    (Metric.ball p₀ ε) Metric.isOpen_ball _).mpr
  simpa only [littlePeriodicCAlphaTorusValue_lift] using
    ha.contDiffOn_of_completeSpace (n := ω)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_holder_native_joint_analytic
