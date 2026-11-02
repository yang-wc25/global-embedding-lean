import Initialization.Geometry.CoordinateComparisons

/-! All-order uniform jets of the genuine fixed coordinate extensions. -/

open Set Metric Filter Manifold IsManifold Topology
open scoped ContDiff Manifold

noncomputable section
namespace GlobalEmbedding.Initialization

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]

/-- A single actual extension family and one derivative sequence work for all
fixed parent-chart pairs. All constants are constructed before any scale. -/
theorem exists_prepared_coordinate_extension_jets (G : PreparedCharts M n) :
    ∃ (ext : Fin G.count → M → EuclideanSpace ℝ (Fin n)) (B : ℕ → ℝ),
      (∀ j, 0 ≤ B j) ∧
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (ext i)) ∧
      (∀ i x, x ∈ (G.chart i).source →
        G.chart i x ∈ closedBall (G.center i) (2 * G.radius i) → ext i x = G.chart i x) ∧
      ∀ i k j y, y ∈ closedBall (G.center i) (2 * G.radius i) →
        ‖iteratedFDeriv ℝ j (ext k ∘ (G.chart i).symm) y‖ ≤ B j := by
  classical
  obtain ⟨ext, _L, _hL, hext, heq, _hcompare⟩ := exists_prepared_coordinate_comparisons G
  have hcore (i : Fin G.count) :
      closedBall (G.center i) (2 * G.radius i) ⊆ (G.chart i).target :=
    (closedBall_subset_closedBall (by linarith [G.radius_pos i])).trans (G.buffered i)
  have each (ik : Fin G.count × Fin G.count) :=
    exists_coordinate_extension_pullback_bounds (ext ik.2) (hext ik.2)
      (G.chart ik.1) (G.chart_smooth ik.1)
      (isCompact_closedBall (G.center ik.1) (2 * G.radius ik.1)) (hcore ik.1)
  choose C hC hbound using each
  refine ⟨ext, fun j ↦ ∑ ik, C ik j, ?_, hext, heq, ?_⟩
  · intro j
    exact Finset.sum_nonneg (fun ik _ ↦ hC ik j)
  · intro i k j y hy
    exact (hbound (i, k) j y hy).trans
      (Finset.single_le_sum (fun ik _ ↦ hC ik j) (Finset.mem_univ (i, k)))

omit [CompactSpace M] in
/-- Equality on the fixed compact two-radius core gives a genuine equality
germ at every point of its interior. This is the locality fact used for true
chart transitions and for cutoffs including their support boundary. -/
theorem prepared_coordinate_extension_eventuallyEq
    (G : PreparedCharts M n)
    (ext : Fin G.count → M → EuclideanSpace ℝ (Fin n))
    (heq : ∀ i x, x ∈ (G.chart i).source →
      G.chart i x ∈ closedBall (G.center i) (2 * G.radius i) → ext i x = G.chart i x)
    (i : Fin G.count) {x : M} (hxs : x ∈ (G.chart i).source)
    (hxc : G.chart i x ∈ ball (G.center i) (2 * G.radius i)) :
    ext i =ᶠ[𝓝 x] G.chart i := by
  filter_upwards [((G.chart i).isOpen_inter_preimage isOpen_ball).mem_nhds ⟨hxs, hxc⟩]
    with z hz
  exact heq i z hz.1 (ball_subset_closedBall hz.2)

/-- Subtracting a fixed center does not affect any positive-order actual jet.
Only local smoothness is used. -/
theorem iteratedFDeriv_sub_fixed_center
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (p : F) {j : ℕ} (hj : j ≠ 0) (x : E)
    (hf : ContDiffAt ℝ j f x) :
    iteratedFDeriv ℝ j (fun z ↦ f z - p) x = iteratedFDeriv ℝ j f x := by
  change iteratedFDeriv ℝ j (f - fun _ ↦ p) x = _
  rw [iteratedFDeriv_sub_apply hf contDiffAt_const, iteratedFDeriv_const_of_ne hj]
  simp

end GlobalEmbedding.Initialization
