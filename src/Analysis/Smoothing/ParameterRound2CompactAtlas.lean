import GlobalEmbedding.Paper.BufferedAtlas
import GlobalEmbedding.Paper.BalancedCompactBaseChartCover
import GlobalEmbedding.Offline.BufferedSamplingDomains
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Algebra.Order.Field.Pi

/-!
# Actual finite buffered atlases on the full compact parameter manifold

Source: the compact-parameter-manifold clause of thm:repair (main.tex 686,
778), and the compact parameter torus used for the probes (main.tex 877).

Reuse the already accepted actual compact chart-cover theorem. Each closed
coordinate ball lies in its real open chart target, so a positive closed
thickening remains there. Finiteness supplies one positive common buffer.
The resulting atlas covers all of the same P, and its true sampling buffers
have compact supersets contained in their actual chart targets. This is a
construction, not an extra atlas-existence premise. It includes empty P and
a zero-dimensional parameter model.
-/

open Set Metric Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff
namespace GlobalEmbedding.Continuation
noncomputable section

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace P] [ChartedSpace E P]
    [IsManifold 𝓘(ℝ, E) ∞ P] [CompactSpace P]

/-- An actual full smooth buffered atlas, with genuine compact norm domains
containing the closure of every fixed sampling buffer. No global-coordinate
chart, nonempty parameter space, or positive parameter dimension is assumed. -/
theorem parameterRound2_exists_compact_bufferedAtlas :
    ∃ A : BufferedAtlas P E, IsSmoothBufferedAtlas A ∧
      ∃ Omega : Fin A.count → Set E,
        ∀ i, IsCompact (Omega i) ∧ Omega i ⊆ (A.chart i).target ∧
          closure (bufferedSamplingCoordinates A i) ⊆ Omega i := by
  classical
  obtain ⟨centers, index, radius, hballs, hcover⟩ :=
    balanced_compact_base_chart_cover (E := E) (B := P)
      (fun _ : Unit => (univ : Set P)) (fun _ => isOpen_univ)
      (fun _ => ⟨(), Set.mem_univ _⟩)
  have hthick (p : P) : ∃ delta : ℝ, 0 < delta ∧
      cthickening delta (closedBall (chartAt E p p) (radius p)) ⊆ (chartAt E p).target :=
    (hballs p).2.2.1.exists_cthickening_subset_open (chartAt E p).open_target
      (fun z hz => ((hballs p).2.2.2 hz).1)
  choose delta hdelta hthick_subset using hthick
  obtain ⟨eps, heps, hsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : centers => (0 : ℝ)) (y := fun p : centers => delta p.val)
    (fun p => hdelta p.val)
  let c : Fin (Fintype.card centers) → P := fun i => ((Fintype.equivFin centers).symm i).val
  let inner (p : P) : Set P := (chartAt E p).source ∩
    (chartAt E p) ⁻¹' ball (chartAt E p p) (radius p)
  let normDomain (p : P) : Set E := cthickening (delta p)
    (closedBall (chartAt E p p) (radius p))
  have hball (i : Fin (Fintype.card centers)) {z : E}
      (hz : z ∈ ball (chartAt E (c i) (c i)) (radius (c i))) :
      ball z eps ⊆ normDomain (c i) := by
    have hepsdelta : eps ≤ delta (c i) := by
      exact le_of_lt (by simpa only [zero_add] using hsmall ((Fintype.equivFin centers).symm i))
    exact (ball_subset_thickening (ball_subset_closedBall hz) eps).trans
      ((thickening_subset_cthickening eps _).trans (cthickening_mono hepsdelta _))
  let A : BufferedAtlas P E := {
    count := Fintype.card centers
    chart := fun i => chartAt E (c i)
    inner := fun i => inner (c i)
    inner_open := fun i => (chartAt E (c i)).isOpen_inter_preimage isOpen_ball
    inner_subset := fun _ _ hx => hx.1
    cover := by
      intro x
      obtain ⟨p, hp, hpx⟩ := hcover x
      refine ⟨(Fintype.equivFin centers) ⟨p, hp⟩, ?_⟩
      simpa only [c, inner, Equiv.symm_apply_apply, Set.mem_inter_iff, Set.mem_preimage] using hpx
    buffer := eps
    buffer_pos := heps
    buffered := by
      intro i x hx
      exact (hball i hx.2).trans (hthick_subset (c i))
    support := fun i => inner (c i) }
  refine ⟨A, ⟨?_, ?_⟩, fun i => normDomain (c i), ?_⟩
  · intro i
    exact IsManifold.chart_mem_maximalAtlas (c i)
  · intro i x hx
    exact hx.1
  · intro i
    refine ⟨(hballs (c i)).2.2.1.cthickening, hthick_subset (c i), ?_⟩
    apply closure_minimal _ isClosed_cthickening
    intro y hy
    obtain ⟨z, hz⟩ := mem_iUnion.mp hy
    obtain ⟨hzInner, hyball⟩ := mem_iUnion.mp hz
    have hzball : z ∈ ball (chartAt E (c i) (c i)) (radius (c i)) := by
      have h := hzInner.2.2
      change chartAt E (c i) ((chartAt E (c i)).symm z) ∈
        ball (chartAt E (c i) (c i)) (radius (c i)) at h
      simpa only [(chartAt E (c i)).right_inv hzInner.1] using h
    exact hball i hzball hyball

#print axioms parameterRound2_exists_compact_bufferedAtlas
end
end GlobalEmbedding.Continuation
