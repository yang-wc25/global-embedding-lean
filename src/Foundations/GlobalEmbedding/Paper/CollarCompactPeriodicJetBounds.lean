import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual compact periodic complex neighborhoods with uniform joint-jet bounds

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Complex finite-dimensional domains are locally compact.
-/

open Set Filter Metric
open scoped Topology

namespace GlobalEmbedding.Paper

/-- A compact subset of an actual periodic analytic complex open domain has a positive compact
closed thickening still in that domain. Every joint derivative is uniformly bounded on all
period translates of the thickening.

Source: Proposition `prop:collar`, proof lines 530–534. Compactness and openness give a positive
closed thickening inside the domain; local compactness allows the thickening to remain compact.
Every joint derivative is analytic and hence continuous there, so its actual operator norm is
bounded. Actual periodicity on the open domain gives equality of the function germs under
translation. Differentiate those germs and use the exact translation chain rule to get equality
of every actual derivative at all translates. This transports the compact bounds over all
periods, including the function and its first three spatial derivatives as special cases. -/
theorem collar_compact_periodic_jet_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [LocallyCompactSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {Γ : Type*} [AddCommGroup Γ]
    (T : Γ →+ E) (g : E → F) (U K : Set E) (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hinv : ∀ z t, z + T t ∈ U ↔ z ∈ U)
    (hperiod : ∀ z ∈ U, ∀ t, g (z + T t) = g z) :
    ∃ δ : ℝ, 0 < δ ∧ IsCompact (cthickening δ K) ∧ cthickening δ K ⊆ U ∧
      ∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ cthickening δ K, ∀ t,
        z + T t ∈ U ∧ ‖iteratedFDeriv ℂ j g (z + T t)‖ ≤ M := by
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨η, hη, hηcompact⟩ := hK.exists_isCompact_cthickening
  let δ := min ε η
  have hδ : 0 < δ := lt_min hε hη
  have hctU : cthickening δ K ⊆ U := (cthickening_mono (min_le_left _ _) K).trans hεU
  have hcompact : IsCompact (cthickening δ K) :=
    hηcompact.of_isClosed_subset isClosed_cthickening (cthickening_mono (min_le_right _ _) K)
  refine ⟨δ, hδ, hcompact, hctU, ?_⟩
  intro j
  have hc : ContinuousOn (iteratedFDeriv ℂ j g) (cthickening δ K) := by
    intro z hz
    exact ((hg.iteratedFDeriv j) z (hctU hz)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hc
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro z hz t
  refine ⟨(hinv z t).mpr (hctU hz), ?_⟩
  have he : (fun w ↦ g (w + T t)) =ᶠ[𝓝 z] g := by
    filter_upwards [hU.mem_nhds (hctU hz)] with w hw
    exact hperiod w hw t
  have hd := (he.iteratedFDeriv ℂ j).eq_of_nhds
  rw [iteratedFDeriv_comp_add_right] at hd
  rw [hd]
  exact (hM z hz).trans (le_max_left _ _)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_compact_periodic_jet_bounds
