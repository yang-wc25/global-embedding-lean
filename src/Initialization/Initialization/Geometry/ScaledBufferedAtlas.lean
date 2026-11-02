import Initialization.Geometry.PreparedCharts
import Initialization.Geometry.RescaledCharts

/-!
# Actual scale-T⁻¹ buffered atlases

The fixed chart-core nets are refined at the real scale T. Their native charts
are y = T (e(x)-p), not hypothetical chart maps. The inner domains cover M and
the buffer is the same positive number ρ/2 for every T≥1. Enlarged supports
are the genuine closed coordinate balls of radius ρ/(4T).
-/

open Set Metric Manifold IsManifold Topology
open scoped ContDiff Manifold

noncomputable section
namespace GlobalEmbedding.Initialization

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

def ChartCutoffFamily.enlargedSupport {G : PreparedCharts M n} {T : ℝ}
    (F : ChartCutoffFamily G T) (i : Fin F.count) : Set M :=
  (G.chart (F.parent i)).source ∩ (G.chart (F.parent i)) ⁻¹'
    closedBall (F.center i) (G.scaleRadius / (4 * T))

def ChartCutoffFamily.innerDomain {G : PreparedCharts M n} {T : ℝ}
    (F : ChartCutoffFamily G T) (i : Fin F.count) : Set M :=
  (G.chart (F.parent i)).source ∩ (G.chart (F.parent i)) ⁻¹'
    ball (F.center i) (G.scaleRadius / (10 * T))

/-- Every enlarged support stays in a fixed compact two-radius parent core. -/
theorem ChartCutoffFamily.enlargedSupport_in_core
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (i : Fin F.count) {x : M} (hx : x ∈ F.enlargedSupport i) :
    G.chart (F.parent i) x ∈
      closedBall (G.center (F.parent i)) (2 * G.radius (F.parent i)) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hsmall : G.scaleRadius / (4 * T) ≤ G.scaleRadius := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * T)).2
    nlinarith [G.scaleRadius_pos]
  have h1 : dist (G.chart (F.parent i) x) (F.center i) ≤ G.scaleRadius / (4 * T) := hx.2
  have h2 : dist (F.center i) (G.center (F.parent i)) ≤ G.radius (F.parent i) := F.center_core i
  have htriangle := dist_triangle (G.chart (F.parent i) x) (F.center i) (G.center (F.parent i))
  rw [mem_closedBall]
  linarith [G.scaleRadius_le (F.parent i)]

/-- The enlarged closed supports actually stay strictly inside those fixed
cores, so coordinate-extension identities hold on neighborhoods of them. -/
theorem ChartCutoffFamily.enlargedSupport_in_open_core
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (i : Fin F.count) {x : M} (hx : x ∈ F.enlargedSupport i) :
    G.chart (F.parent i) x ∈
      ball (G.center (F.parent i)) (2 * G.radius (F.parent i)) := by
  have hsmall : G.scaleRadius / (4 * T) < G.scaleRadius :=
    (GlobalEmbedding.Offline.scaledCutoffProfile_radius_nesting
      G.scaleRadius T G.scaleRadius_pos hT).2.2
  have h1 : dist (G.chart (F.parent i) x) (F.center i) ≤ G.scaleRadius / (4 * T) := hx.2
  have h2 : dist (F.center i) (G.center (F.parent i)) ≤ G.radius (F.parent i) := F.center_core i
  have htriangle := dist_triangle (G.chart (F.parent i) x) (F.center i) (G.center (F.parent i))
  rw [mem_ball]
  linarith [G.scaleRadius_le (F.parent i)]

theorem ChartCutoffFamily.coordinate_closedBall_subset_target
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (i : Fin F.count) :
    closedBall (F.center i) (G.scaleRadius / (4 * T)) ⊆ (G.chart (F.parent i)).target := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  intro y hy
  apply G.buffered (F.parent i)
  have hcore := F.center_core i
  rw [mem_closedBall] at hy hcore ⊢
  have hsmall : G.scaleRadius / (4 * T) ≤ G.scaleRadius := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * T)).2
    nlinarith [G.scaleRadius_pos]
  have htriangle := dist_triangle y (F.center i) (G.center (F.parent i))
  linarith [G.scaleRadius_le (F.parent i), G.radius_pos (F.parent i)]

/-- The atlas itself is explicitly constructed using the original native
`BufferedAtlas`; its buffer does not depend on the scale. -/
def ChartCutoffFamily.scaledAtlas {G : PreparedCharts M n} {T : ℝ}
    (F : ChartCutoffFamily G T) (hT : 1 ≤ T) :
    GlobalEmbedding.Paper.BufferedAtlas M (EuclideanSpace ℝ (Fin n)) where
  count := F.count
  chart := fun i ↦ rescaledChart (G.chart (F.parent i)) (F.center i) T
    (ne_of_gt (zero_lt_one.trans_le hT))
  inner := F.innerDomain
  inner_open := fun i ↦ (G.chart (F.parent i)).isOpen_inter_preimage isOpen_ball
  inner_subset := fun _ _ hx ↦ hx.1
  cover := F.net_cover
  buffer := G.scaleRadius / 2
  buffer_pos := half_pos G.scaleRadius_pos
  buffered := by
    intro i x hx y hy
    apply rescaledChart_closedBall_buffer (G.chart (F.parent i))
      (G.radius_pos (F.parent i)) (G.scaleRadius_le (F.parent i))
      (F.center_core i) (G.buffered (F.parent i)) hT
    have hTpos : 0 < T := zero_lt_one.trans_le hT
    let eT := rescaledChart (G.chart (F.parent i)) (F.center i) T hTpos.ne'
    have hxnorm : ‖eT x‖ < G.scaleRadius / 10 := by
      rw [norm_rescaledChart _ _ hTpos]
      have hd : dist (G.chart (F.parent i) x) (F.center i) < G.scaleRadius / (10 * T) := hx.2
      have hm := mul_lt_mul_of_pos_left hd hTpos
      have heq : T * (G.scaleRadius / (10 * T)) = G.scaleRadius / 10 := by field_simp
      exact heq ▸ hm
    have hyn : dist y (eT x) < G.scaleRadius / 2 := hy
    have htriangle := dist_triangle y (eT x) 0
    rw [mem_closedBall, dist_zero_right]
    simp only [dist_zero_right] at htriangle
    linarith [G.scaleRadius_pos]
  support := F.enlargedSupport

theorem ChartCutoffFamily.scaledAtlas_smooth
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T) :
    GlobalEmbedding.Paper.IsSmoothBufferedAtlas (F.scaledAtlas hT) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact rescaledChart_mem_maximalAtlas (G.chart (F.parent i))
      (G.chart_smooth (F.parent i)) (F.center i) T
      (ne_of_gt (zero_lt_one.trans_le hT))
  · exact fun _ _ hx ↦ hx.1

theorem ChartCutoffFamily.enlargedSupport_compact
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (i : Fin F.count) : IsCompact (F.enlargedSupport i) := by
  have htarget := F.coordinate_closedBall_subset_target hT i
  have heq : F.enlargedSupport i = (G.chart (F.parent i)).symm ''
      closedBall (F.center i) (G.scaleRadius / (4 * T)) := by
    ext x
    constructor
    · intro hx
      exact ⟨G.chart (F.parent i) x, hx.2, (G.chart (F.parent i)).left_inv hx.1⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(G.chart (F.parent i)).map_target (htarget hy), by
        simpa only [Set.mem_preimage, (G.chart (F.parent i)).right_inv (htarget hy)] using hy⟩
  rw [heq]
  exact (isCompact_closedBall _ _).image_of_continuousOn
    ((G.chart (F.parent i)).continuousOn_symm.mono htarget)

theorem ChartCutoffFamily.scaledAtlas_inner_subset_support
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (i : Fin F.count) : (F.scaledAtlas hT).inner i ⊆ (F.scaledAtlas hT).support i := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hd : dist (G.chart (F.parent i) x) (F.center i) < G.scaleRadius / (10 * T) := hx.2
  change dist (G.chart (F.parent i) x) (F.center i) ≤ G.scaleRadius / (4 * T)
  apply hd.le.trans
  apply div_le_div_of_nonneg_left G.scaleRadius_pos.le (by positivity)
  nlinarith

theorem ChartCutoffFamily.scaledAtlas_support_coordinate_bound
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (i : Fin F.count) {x : M} (hx : x ∈ (F.scaledAtlas hT).support i) :
    ‖(F.scaledAtlas hT).chart i x‖ ≤ G.scaleRadius / 4 := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  change ‖rescaledChart _ _ T hTpos.ne' x‖ ≤ _
  rw [norm_rescaledChart _ _ hTpos]
  have hd : dist (G.chart (F.parent i) x) (F.center i) ≤ G.scaleRadius / (4 * T) := hx.2
  have hm := mul_le_mul_of_nonneg_left hd hTpos.le
  have heq : T * (G.scaleRadius / (4 * T)) = G.scaleRadius / 4 := by field_simp
  exact heq ▸ hm

/-- Actual all-scale buffered atlases exist after the fixed preparation. -/
theorem exists_compact_allScale_buffered_atlases [CompactSpace M] :
    ∃ (G : PreparedCharts M n), ∀ T : ℝ, ∀ hT : 1 ≤ T,
      ∃ F : ChartCutoffFamily G T,
        GlobalEmbedding.Paper.IsSmoothBufferedAtlas (F.scaledAtlas hT) ∧
        (∀ i, IsCompact ((F.scaledAtlas hT).support i)) ∧
        (F.scaledAtlas hT).buffer = G.scaleRadius / 2 := by
  obtain ⟨G⟩ := exists_preparedCharts (M := M) (n := n)
  refine ⟨G, ?_⟩
  intro T hT
  obtain ⟨F⟩ := exists_chartCutoffFamily G hT
  exact ⟨F, F.scaledAtlas_smooth hT, F.enlargedSupport_compact hT, rfl⟩

end GlobalEmbedding.Initialization
