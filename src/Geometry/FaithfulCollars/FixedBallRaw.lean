import FaithfulCollars.FixedBallGeometry
import GlobalEmbedding.Offline.ScaledChartBumps
import Smoothing.TensorSetupProviders

/-!
# Actual raw covering bumps on the original fixed buffered balls

Source: `setup:uniform` and `thm:repair`, main.tex 591 and 698.  The actual
formula is the already accepted fixed bump pulled back by each ORIGINAL
chart and extended by zero.  All-order own-chart constants are selected
before the atlas, with no dependence on its number of charts.

Unlike the older raw record, the function is not required to have support
inside the covering inner ball: it equals one there, and its support lies
in the original enlarged support and original sampling buffer.  These are
proved from the geometric radii; none is an input estimate for the output.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]

def originalBallRaw (A : BufferedAtlas M E) (rho : ℝ) (i : Fin A.count) : M → ℝ :=
  scaledChartCutoff rho 1 (A.chart i)

variable {A : BufferedAtlas M E} {rho : ℝ} (g : OriginalFixedBallGeometry A rho)

include g

/-- Only the actual support ball has to be compactly contained in the chart
target.  No compactness of the target or any norm domain is asserted. -/
theorem originalBallRaw_compact_support (i : Fin A.count) :
    HasCompactSupport (originalBallRaw A rho i) ∧
    tsupport (originalBallRaw A rho i) ⊆
      (A.chart i).source ∩ (A.chart i) ⁻¹' closedBall 0 (3 * rho / 20) := by
  let e := A.chart i
  have ht : closedBall (0 : E) (3 * rho / 20) ⊆ e.target :=
    (closedBall_subset_closedBall (by linarith [g.radius_pos])).trans (g.target_buffer i)
  have hc : IsCompact (e.symm '' closedBall (0 : E) (3 * rho / 20)) :=
    (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono ht)
  have hs : Function.support (originalBallRaw A rho i) =
      e.source ∩ e ⁻¹' ball 0 (3 * rho / 20) := by
    simp only [originalBallRaw, scaledChartCutoff, support_indicator,
      Function.support_comp_eq_preimage, scaledCutoffProfile_support rho 1 g.radius_pos le_rfl,
      mul_one, e]
  have hsub : Function.support (originalBallRaw A rho i) ⊆
      e.symm '' closedBall 0 (3 * rho / 20) := by
    intro x hx
    rw [hs] at hx
    exact ⟨e x, ball_subset_closedBall hx.2, e.left_inv hx.1⟩
  have hts : tsupport (originalBallRaw A rho i) ⊆
      e.symm '' closedBall 0 (3 * rho / 20) := closure_minimal hsub hc.isClosed
  refine ⟨hc.of_isClosed_subset (isClosed_tsupport _) hts, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hts hx
  refine ⟨e.map_target (ht hy), ?_⟩
  change e (e.symm y) ∈ closedBall 0 (3 * rho / 20)
  rw [e.right_inv (ht hy)]
  exact hy

theorem originalBallRaw_enlarged_support (i : Fin A.count) :
    tsupport (originalBallRaw A rho i) ⊆ A.support i := by
  intro x hx
  have h := (originalBallRaw_compact_support g i).2 hx
  exact g.small_carrier_support i h.1 h.2

theorem originalBallRaw_original_sampling (i : Fin A.count) :
    MapsTo (A.chart i) (tsupport (originalBallRaw A rho i))
      (bufferedSamplingCoordinates A i) := by
  intro x hx
  apply g.ball_subset_original_sampling i
  exact (closedBall_subset_ball (by linarith [g.radius_pos]))
    ((originalBallRaw_compact_support g i).2 hx).2

theorem originalBallRaw_plateau_cover (x : M) :
    ∃ i, originalBallRaw A rho i x = 1 := by
  obtain ⟨i, hi⟩ := A.cover x
  rw [g.inner_eq i] at hi
  refine ⟨i, scaledChartCutoff_one rho 1 g.radius_pos le_rfl (A.chart i) ?_⟩
  simpa only [mul_one] using ⟨hi.1, ball_subset_closedBall hi.2⟩

variable [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem originalBallRaw_smooth (hA : IsSmoothBufferedAtlas A) (i : Fin A.count) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (originalBallRaw A rho i) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hxs := ((originalBallRaw_compact_support g i).2 hx).1
  have hs := (scaledCutoffProfile_contDiff (E := E) rho 1).contMDiff.contMDiffAt.comp x
    (contMDiffAt_of_mem_maximalAtlas (hA.chart_mem i) hxs)
  apply hs.congr_of_eventuallyEq
  filter_upwards [(A.chart i).open_source.mem_nhds hxs] with y hy
  exact scaledChartCutoff_on_source rho 1 (A.chart i) hy

omit g in
/-- The profile is chosen before ANY atlas or observation order.  The same
literal raw functions satisfy all own-chart estimates simultaneously. -/
theorem exists_uniform_originalBallRaw_jets (rho : ℝ) (hrho : 0 < rho) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (A : BufferedAtlas M E) (i : Fin A.count) (j : ℕ) (y : E),
        y ∈ (A.chart i).target →
        ‖iteratedFDeriv ℝ j (originalBallRaw A rho i ∘ (A.chart i).symm) y‖ ≤ B j := by
  obtain ⟨B, hB, hjet⟩ := exists_scaledCutoffProfile_derivative_bounds (E := E) rho hrho
  refine ⟨B, hB, ?_⟩
  intro A i j y hy
  rw [originalBallRaw, iteratedFDeriv_scaledChartCutoff rho 1 (A.chart i) j hy]
  simpa only [one_pow, mul_one] using hjet 1 le_rfl j y

theorem originalBallRaw_local_count (D : ℕ) (hD : A.supportDegree ≤ D) (x : M) :
    (activeCutoffIndices (originalBallRaw A rho) x).card ≤ D + 1 := by
  apply activeCutoffIndices_card_le_enlarged_degree A.support (originalBallRaw A rho)
    (originalBallRaw_enlarged_support g) D _ x
  intro i
  classical
  change A.supportGraph.degree i ≤ D
  exact (Finset.le_sup (f := fun j => A.supportGraph.degree j) (Finset.mem_univ i)).trans hD

end GlobalEmbedding.Continuation.FaithfulCollars
