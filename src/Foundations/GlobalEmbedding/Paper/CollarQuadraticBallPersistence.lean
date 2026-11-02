import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.OrderClosed

/-!
# Persistence of an actual real quadratic ball under continuous parameter changes

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. This constructs the common real ball from strict estimates at the base.
-/

open Set Filter
open scoped Topology NNReal

namespace GlobalEmbedding.Paper

/-- Strict base-point quadratic norm estimates persist on one original real norm ball for all
sufficiently near parameters, with the specified Lipschitz constant q.

Source: Proposition `prop:collar`, proof lines 530–534, shrinking the coefficient neighborhood.
The two scalar expressions controlling the image norm and the Lipschitz constant are continuous
at the base point. Their strict inequalities therefore hold on one common parameter neighborhood.
Actual continuous-linear/bilinear operator norm inequalities bound the original map on the ball.
Bilinearity gives B(u,u)-B(v,v)=B(u-v,u)+B(v,u-v), without a symmetry assumption. Norm bounds on
both ball points give the actual Lipschitz constant 2 norm(A) norm(B) rho, which is below q.
Neither completeness, a complex norm contraction, a preexisting common neighborhood nor actual
contraction estimates for the source Q are assumed proved by this generic persistence step. -/
theorem collar_quadratic_ball_persistence
    {P X Y : Type*} [TopologicalSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : P → Y →L[ℝ] X) (f : P → X) (B : X →L[ℝ] X →L[ℝ] Y) (p₀ : P)
    (hA : ContinuousAt A p₀) (hf : ContinuousAt f p₀)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (q : ℝ≥0)
    (himage : ‖f p₀‖ + ‖A p₀‖ * ‖B‖ * ρ ^ 2 < ρ)
    (hlip : 2 * ‖A p₀‖ * ‖B‖ * ρ < (q : ℝ)) :
    ∀ᶠ p in 𝓝 p₀,
      let S : Set X := {x | ‖x‖ ≤ ρ}
      let Φ := fun x ↦ f p + A p (B x x)
      MapsTo Φ S S ∧ LipschitzOnWith q Φ S := by
  have hc₁ : ContinuousAt (fun p ↦ ‖f p‖ + ‖A p‖ * ‖B‖ * ρ ^ 2) p₀ :=
    hf.norm.add ((hA.norm.mul continuousAt_const).mul continuousAt_const)
  have hc₂ : ContinuousAt (fun p ↦ 2 * ‖A p‖ * ‖B‖ * ρ) p₀ :=
    ((continuousAt_const.mul hA.norm).mul continuousAt_const).mul continuousAt_const
  filter_upwards [hc₁.eventually_lt continuousAt_const himage,
    hc₂.eventually_lt continuousAt_const hlip] with p hp₁ hp₂
  dsimp only
  let K := ‖A p‖ * ‖B‖
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg (A p)) (norm_nonneg B)
  have hbound (u v : X) : ‖A p (B u v)‖ ≤ K * ‖u‖ * ‖v‖ := by
    calc
      ‖A p (B u v)‖ ≤ ‖A p‖ * ‖B u v‖ := (A p).le_opNorm _
      _ ≤ ‖A p‖ * (‖B‖ * ‖u‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (B.le_opNorm₂ u v) (norm_nonneg (A p))
      _ = K * ‖u‖ * ‖v‖ := by dsimp only [K]; ring
  constructor
  · intro u hu
    change ‖f p + A p (B u u)‖ ≤ ρ
    change ‖u‖ ≤ ρ at hu
    calc
      ‖f p + A p (B u u)‖ ≤ ‖f p‖ + ‖A p (B u u)‖ := norm_add_le _ _
      _ ≤ ‖f p‖ + K * ‖u‖ * ‖u‖ := add_le_add le_rfl (hbound u u)
      _ ≤ ‖f p‖ + K * ρ ^ 2 := by
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul hu hu (norm_nonneg u) hρ) hK
        nlinarith
      _ ≤ ρ := hp₁.le
  · apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    change ‖u‖ ≤ ρ at hu
    change ‖v‖ ≤ ρ at hv
    have he : (f p + A p (B u u)) - (f p + A p (B v v)) =
        A p (B (u - v) u) + A p (B v (u - v)) := by
      simp only [map_sub, sub_apply]
      abel
    rw [dist_eq_norm, dist_eq_norm, he]
    calc
      ‖A p (B (u - v) u) + A p (B v (u - v))‖ ≤
          ‖A p (B (u - v) u)‖ + ‖A p (B v (u - v))‖ := norm_add_le _ _
      _ ≤ K * ‖u - v‖ * ‖u‖ + K * ‖v‖ * ‖u - v‖ :=
        add_le_add (hbound (u - v) u) (hbound v (u - v))
      _ ≤ K * ‖u - v‖ * ρ + K * ρ * ‖u - v‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hu (mul_nonneg hK (norm_nonneg _)))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hK) (norm_nonneg _))
      _ = (2 * ‖A p‖ * ‖B‖ * ρ) * ‖u - v‖ := by dsimp only [K]; ring
      _ ≤ (q : ℝ) * ‖u - v‖ :=
        mul_le_mul_of_nonneg_right hp₂.le (norm_nonneg _)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_quadratic_ball_persistence
