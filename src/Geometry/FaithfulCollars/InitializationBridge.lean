import FaithfulCollars.OriginalBallCollars
import Initialization.Geometry.RawCutoffGeometry
import Initialization.Geometry.BoundedScaledAtlas

/-!
# The accepted original atlas construction supplies the faithful geometry

This proves every fixed-ball field from the existing actual initialization
atlas.  No chart, enlarged support, inner, scale or norm domain is replaced.
Thus the corrected raw support contract applies to a genuine existing
producer, not just an independently assumed geometric record.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Initialization
open Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T)

theorem initialization_scaledAtlas_fixed_ball_geometry :
    OriginalFixedBallGeometry (F.scaledAtlas hT) G.scaleRadius := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  refine ⟨G.scaleRadius_pos, ?_, ?_, ?_, ?_⟩
  · intro i
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, by simpa only [Set.mem_preimage, mem_ball, dist_zero_right] using
        F.scaledAtlas_inner_coordinate_bound hT i hx⟩
    · rintro ⟨hxs, hxn⟩
      refine ⟨hxs, ?_⟩
      have hn : ‖rescaledChart (G.chart (F.parent i)) (F.center i) T hTp.ne' x‖ <
          G.scaleRadius / 10 := by
        simpa only [Set.mem_preimage, mem_ball, dist_zero_right, ChartCutoffFamily.scaledAtlas] using hxn
      rw [norm_rescaledChart _ _ hTp] at hn
      change dist (G.chart (F.parent i) x) (F.center i) < G.scaleRadius / (10 * T)
      apply (lt_div_iff₀ (by positivity : 0 < 10 * T)).mpr
      nlinarith
  · intro i
    exact (closedBall_subset_closedBall (by linarith [G.scaleRadius_pos])).trans
      (rescaledChart_closedBall_buffer (G.chart (F.parent i)) (G.radius_pos _)
        (G.scaleRadius_le _) (F.center_core i) (G.buffered _) hT)
  · intro i x hx
    refine ⟨hx.1, ?_⟩
    have hn : ‖rescaledChart (G.chart (F.parent i)) (F.center i) T hTp.ne' x‖ ≤
        G.scaleRadius / 4 := by
      simpa only [Set.mem_preimage, mem_closedBall, dist_zero_right, ChartCutoffFamily.scaledAtlas] using hx.2
    rw [norm_rescaledChart _ _ hTp] at hn
    change dist (G.chart (F.parent i) x) (F.center i) ≤ G.scaleRadius / (4 * T)
    apply (le_div_iff₀ (by positivity : 0 < 4 * T)).mpr
    nlinarith
  · change G.scaleRadius / 4 ≤ G.scaleRadius / 2
    linarith [G.scaleRadius_pos]

theorem initialization_boundedAtlas_fixed_ball_geometry :
    OriginalFixedBallGeometry (F.boundedAtlas hT) G.scaleRadius := by
  have gs := initialization_scaledAtlas_fixed_ball_geometry F hT
  refine ⟨G.scaleRadius_pos, ?_, ?_, ?_, ?_⟩
  · intro i
    ext x
    constructor
    · intro hx
      refine ⟨(F.boundedAtlas hT).inner_subset i hx, ?_⟩
      exact ((gs.inner_eq i ▸ hx).2)
    · rintro ⟨hxs, hxsmall⟩
      apply (Set.ext_iff.mp (gs.inner_eq i) x).mpr
      exact ⟨hxs.1, hxsmall⟩
  · intro i
    change closedBall (0 : EuclideanSpace ℝ (Fin n)) (G.scaleRadius / 4) ⊆
      ball 0 G.scaleRadius
    exact closedBall_subset_ball (by linarith [G.scaleRadius_pos])
  · intro i x hx
    exact gs.enlarged_support i ⟨hx.1.1, hx.2⟩
  · exact gs.buffer_lower

/-- The raw expression in the new bridge is the SAME original actual raw
cutoff, under its already existing rescaled coordinate chart. -/
theorem initialization_originalBallRaw_eq_rawCutoff (i : Fin F.count) :
    originalBallRaw (F.scaledAtlas hT) G.scaleRadius i = F.rawCutoff i := by
  funext x
  change scaledChartCutoff G.scaleRadius 1
      (rescaledChart (G.chart (F.parent i)) (F.center i) T (zero_lt_one.trans_le hT).ne') x =
    scaledChartCutoff G.scaleRadius T (translatedChart (G.chart (F.parent i)) (F.center i)) x
  by_cases hx : x ∈ (G.chart (F.parent i)).source
  · rw [scaledChartCutoff_on_source G.scaleRadius 1
        (rescaledChart (G.chart (F.parent i)) (F.center i) T (zero_lt_one.trans_le hT).ne') hx,
      scaledChartCutoff_on_source G.scaleRadius T (translatedChart (G.chart (F.parent i)) (F.center i)) hx]
    simp only [scaledCutoffProfile, rescaledChart_apply, translatedChart_apply, smul_smul]
    congr 2
    ring
  · rw [scaledChartCutoff_off_source G.scaleRadius 1
        (rescaledChart (G.chart (F.parent i)) (F.center i) T (zero_lt_one.trans_le hT).ne') hx,
      scaledChartCutoff_off_source G.scaleRadius T (translatedChart (G.chart (F.parent i)) (F.center i)) hx]

/-- The normalized partition also remains the SAME existing function. -/
theorem initialization_originalBallCutoff_eq_cutoff (i : Fin F.count) :
    originalBallCutoff (F.scaledAtlas hT) G.scaleRadius i = F.cutoff i := by
  rw [F.cutoff_eq_normalized_raw i]
  unfold originalBallCutoff
  have hraw : originalBallRaw (F.scaledAtlas hT) G.scaleRadius = F.rawCutoff :=
    funext (initialization_originalBallRaw_eq_rawCutoff F hT)
  rw [hraw]
  rfl

/-- A genuine compact extension of every ORIGINAL bounded chart.  Its
coordinate functions and inverse functions are literally unchanged.  This
is the correct finiteness bridge even when Omega is the whole open target:
the compact carrier belongs to the existing parent chart, not to a shrunken
or replaced original norm domain. -/
theorem initialization_original_chart_compact_extension (i : Fin F.count) :
    ((F.scaledAtlas hT).chart i ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M) ∧
    (↑((F.boundedAtlas hT).chart i) : M → EuclideanSpace ℝ (Fin n)) =
      ↑((F.scaledAtlas hT).chart i) ∧
    (↑((F.boundedAtlas hT).chart i).symm : EuclideanSpace ℝ (Fin n) → M) =
      ↑((F.scaledAtlas hT).chart i).symm ∧
    IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius) ∧
    ((F.boundedAtlas hT).chart i).target ⊆ closedBall 0 G.scaleRadius ∧
    closedBall (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius ⊆
      ((F.scaledAtlas hT).chart i).target := by
  exact ⟨(F.scaledAtlas_smooth hT).chart_mem i, rfl, rfl, isCompact_closedBall _ _,
    ball_subset_closedBall,
    rescaledChart_closedBall_buffer (G.chart (F.parent i)) (G.radius_pos _)
      (G.scaleRadius_le _) (F.center_core i) (G.buffered _) hT⟩

/-- Any original norm set inside the original chart target is controlled by
that actual parent compact extension.  Omega itself is not assumed compact. -/
theorem initialization_original_samples_in_compact_parent
    (Omega : Fin F.count → Set (EuclideanSpace ℝ (Fin n)))
    (hOmega : ∀ i, Omega i ⊆ ((F.boundedAtlas hT).chart i).target) (i : Fin F.count) :
    Omega i ⊆ closedBall 0 G.scaleRadius ∧
    closedBall (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius ⊆
      ((F.scaledAtlas hT).chart i).target := by
  have h := initialization_original_chart_compact_extension F hT i
  exact ⟨(hOmega i).trans h.2.2.2.2.1, h.2.2.2.2.2⟩

end GlobalEmbedding.Continuation.FaithfulCollars
