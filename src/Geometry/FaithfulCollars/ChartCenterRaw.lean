import FaithfulCollars.CenterRaw
import GlobalEmbedding.Offline.ScaledChartBumps

/-!
# Pulling the manufactured center plateau back through the original chart

This file uses arbitrary original charts.  Only the actual compact raw
carrier must fit in the original target.  No ball is centered at the chart
origin, no original chart is translated and no original norm is altered.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]

def chartCenterRaw (e : OpenPartialHomeomorph M E) (s : Finset E) (r : ℝ) : M → ℝ :=
  e.source.indicator (centerRaw E s r ∘ e)

theorem chartCenterRaw_compact_support (e : OpenPartialHomeomorph M E)
    (s : Finset E) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ s, ∀ c ∈ s, a ≠ c → r ≤ dist a c)
    (hTarget : centerRawCarrier E s r ⊆ e.target) :
    HasCompactSupport (chartCenterRaw e s r) ∧
    tsupport (chartCenterRaw e s r) ⊆ e.source ∩ e ⁻¹' centerRawCarrier E s r := by
  have hc : IsCompact (e.symm '' centerRawCarrier E s r) :=
    (centerRawCarrier_compact E s r).image_of_continuousOn (e.continuousOn_symm.mono hTarget)
  have hsub : Function.support (chartCenterRaw e s r) ⊆ e.symm '' centerRawCarrier E s r := by
    intro x hx
    have hxs : x ∈ e.source := by
      by_contra hn
      exact hx (Set.indicator_of_notMem hn _)
    have hval : centerRaw E s r (e x) ≠ 0 := by
      simpa only [Function.mem_support, chartCenterRaw, Set.indicator_of_mem hxs,
        Function.comp_apply] using hx
    exact ⟨e x, centerRaw_tsupport E s r hr hsep (subset_tsupport _ hval), e.left_inv hxs⟩
  have hts : tsupport (chartCenterRaw e s r) ⊆ e.symm '' centerRawCarrier E s r :=
    closure_minimal hsub hc.isClosed
  refine ⟨hc.of_isClosed_subset (isClosed_tsupport _) hts, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hts hx
  refine ⟨e.map_target (hTarget hy), ?_⟩
  change e (e.symm y) ∈ centerRawCarrier E s r
  rwa [e.right_inv (hTarget hy)]

theorem chartCenterRaw_one_on (e : OpenPartialHomeomorph M E)
    (s : Finset E) (r : ℝ) (hr : 0 < r) (K : Set E)
    (hcover : ∀ y ∈ K, ∃ c ∈ s, dist y c ≤ r)
    {x : M} (hx : x ∈ e.source) (hK : e x ∈ K) :
    chartCenterRaw e s r x = 1 := by
  rw [chartCenterRaw, Set.indicator_of_mem hx]
  exact centerRaw_one_on E s r hr K hcover (e x) hK

theorem chartCenterRaw_own_jets (e : OpenPartialHomeomorph M E)
    (s : Finset E) (r : ℝ) (hr : 0 < r) (L : ℕ)
    (hcard : s.card ≤ L)
    (hsep : ∀ a ∈ s, ∀ c ∈ s, a ≠ c → r ≤ dist a c)
    (j : ℕ) (y : E) (hy : y ∈ e.target) :
    ‖iteratedFDeriv ℝ j (chartCenterRaw e s r ∘ e.symm) y‖ ≤ centerRawProfile E r hr L j := by
  have hgerm : chartCenterRaw e s r ∘ e.symm =ᶠ[𝓝 y] centerRaw E s r := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    simp only [Function.comp_apply, chartCenterRaw, Set.indicator_of_mem (e.map_target hz),
      e.right_inv hz]
  rw [(hgerm.iteratedFDeriv ℝ j).eq_of_nhds]
  exact centerRaw_jets E s r hr L hcard hsep j y

variable [ChartedSpace E M]

theorem chartCenterRaw_smooth (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (s : Finset E) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ s, ∀ c ∈ s, a ≠ c → r ≤ dist a c)
    (hTarget : centerRawCarrier E s r ⊆ e.target) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chartCenterRaw e s r) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hxs := ((chartCenterRaw_compact_support e s r hr hsep hTarget).2 hx).1
  have hs := (centerRaw_contDiff E s r hr hsep).contMDiff.contMDiffAt.comp x
    (contMDiffAt_of_mem_maximalAtlas he hxs)
  apply hs.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hxs] with y hy
  exact Set.indicator_of_mem hy _

end GlobalEmbedding.Continuation.FaithfulCollars
