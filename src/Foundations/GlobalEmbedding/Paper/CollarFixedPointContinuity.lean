import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Linarith

/-!
# Continuity of a uniformly contracting fixed-point family

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. A real fixed-point family must stay near the base fixed point to be
identified with the local analytic branch by implicit-function uniqueness.
-/

open scoped Topology NNReal

namespace GlobalEmbedding.Paper

/-- Fixed points of a uniform family of strict contractions on a common set depend continuously
on the parameter whenever evaluating the maps at the base fixed point does.

Source: Proposition `prop:collar`, proof lines 530–534, analytic branch matching.
Write x=g(p), x₀=g(p₀). The fixed-point equations and the triangle inequality give
`dist(x,x₀) ≤ q*dist(x,x₀) + dist(F(p,x₀),F(p₀,x₀))`.
Since `q<1`, divide by `1-q`. Continuity of the last evaluation at p₀ then proves continuity
of g. Completeness and invariance are needed to construct fixed points, but not for this
continuity statement about an existing family. The common set may have empty interior or be a
singleton; no positive radius or interior fixed point is assumed.
-/
theorem collar_fixed_point_continuity
    {P X : Type*} [TopologicalSpace P] [MetricSpace X]
    (F : P → X → X) (g : P → X) (p₀ : P) (S : Set X)
    (q : ℝ≥0) (hq : (q : ℝ) < 1)
    (hg₀ : g p₀ ∈ S) (hfixed₀ : F p₀ (g p₀) = g p₀)
    (hnear : ∀ᶠ p in 𝓝 p₀, g p ∈ S ∧ F p (g p) = g p ∧ LipschitzOnWith q (F p) S)
    (hcont : ContinuousAt (fun p ↦ F p (g p₀)) p₀) :
    ContinuousAt g p₀ := by
  have hqpos : 0 < 1 - (q : ℝ) := sub_pos.mpr hq
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have heval : ∀ᶠ p in 𝓝 p₀,
      dist (F p (g p₀)) (F p₀ (g p₀)) < ε * (1 - (q : ℝ)) :=
    hcont.eventually_mem (Metric.ball_mem_nhds _ (mul_pos hε hqpos))
  filter_upwards [hnear, heval] with p hp hεp
  have hdist : dist (g p) (g p₀) ≤
      (q : ℝ) * dist (g p) (g p₀) + dist (F p (g p₀)) (F p₀ (g p₀)) := by
    calc
      dist (g p) (g p₀) = dist (F p (g p)) (F p₀ (g p₀)) := by
        rw [hp.2.1, hfixed₀]
      _ ≤ dist (F p (g p)) (F p (g p₀)) + dist (F p (g p₀)) (F p₀ (g p₀)) :=
        dist_triangle _ _ _
      _ ≤ (q : ℝ) * dist (g p) (g p₀) + dist (F p (g p₀)) (F p₀ (g p₀)) :=
        add_le_add (hp.2.2.dist_le_mul (g p) hp.1 (g p₀) hg₀) le_rfl
  have hbound : dist (g p) (g p₀) ≤
      dist (F p (g p₀)) (F p₀ (g p₀)) / (1 - (q : ℝ)) := by
    apply (le_div_iff₀ hqpos).mpr
    nlinarith [hdist]
  exact hbound.trans_lt ((div_lt_iff₀ hqpos).mpr hεp)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_fixed_point_continuity
