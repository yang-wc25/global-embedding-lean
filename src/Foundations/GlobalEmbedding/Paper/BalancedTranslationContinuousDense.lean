import Mathlib.Topology.MetricSpace.Isometry

/-!
# Continuity of isometric families from dense continuous orbits

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
lines 382–418. Abstract metric-space step in the little-Hölder translation argument.
DAG node: `balanced-translation-continuous-dense`.
-/

open Set
open scoped Topology

namespace GlobalEmbedding.Paper

/-- An isometric family whose parameter orbits are continuous on a dense subset is jointly
continuous. No group structure or completeness assumption is needed.

Proof: approximate the target point by a dense-subset point within epsilon/4. Nearby inputs
are also within epsilon/4 of the target point. Continuity of the orbit of the approximating
point makes its two images close within epsilon/4. The triangle inequality and the isometries
bound the resulting image distance by epsilon/4 + 2(epsilon/4) + epsilon/4.
Source: `lem:balanced`, translation-continuity argument, abstract metric-space expansion. -/
theorem balanced_translation_continuous_dense
    {H X : Type*} [TopologicalSpace H] [PseudoMetricSpace X]
    (τ : H → X → X) (hτ : ∀ h, Isometry (τ h))
    (S : Set X) (hS : Dense S) (horbit : ∀ s ∈ S, Continuous (fun h ↦ τ h s)) :
    Continuous (fun z : H × X ↦ τ z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  intro z
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨s, hs, hxs⟩ := Metric.mem_closure_iff.mp (hS z.2) (ε / 4) (by positivity)
  have hparam : ∀ᶠ w : H × X in 𝓝 z, dist (τ w.1 s) (τ z.1 s) < ε / 4 :=
    ((horbit s hs).continuousAt.comp continuousAt_fst).eventually
      (Metric.ball_mem_nhds _ (by positivity))
  have hinput : ∀ᶠ w : H × X in 𝓝 z, dist w.2 z.2 < ε / 4 :=
    continuousAt_snd.eventually (Metric.ball_mem_nhds _ (by positivity))
  filter_upwards [hparam, hinput] with w hwp hwi
  have hdist : dist (τ w.1 w.2) (τ z.1 z.2) ≤
      dist w.2 z.2 + 2 * dist z.2 s + dist (τ w.1 s) (τ z.1 s) := by
    calc
      dist (τ w.1 w.2) (τ z.1 z.2) ≤
          dist (τ w.1 w.2) (τ w.1 s) + dist (τ w.1 s) (τ z.1 s) +
            dist (τ z.1 s) (τ z.1 z.2) := dist_triangle4 _ _ _ _
      _ = dist w.2 s + dist (τ w.1 s) (τ z.1 s) + dist s z.2 := by
        rw [(hτ w.1).dist_eq, (hτ z.1).dist_eq]
      _ ≤ dist w.2 z.2 + 2 * dist z.2 s + dist (τ w.1 s) (τ z.1 s) := by
        have := dist_triangle w.2 z.2 s
        rw [dist_comm s z.2]
        linarith
  linarith

#print axioms balanced_translation_continuous_dense

end GlobalEmbedding.Paper
