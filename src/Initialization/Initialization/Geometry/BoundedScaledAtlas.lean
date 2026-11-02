import Initialization.Geometry.ScaledBufferedAtlas

/-!
# Fixed-radius coordinate domains for the actual scale atlases

Restrict each already constructed rescaled chart to the same ball of radius ρ.
The actual coordinate and inverse functions are unchanged; only their genuine
domains are restricted. Inner domains, compact enlarged supports and the buffer
ρ/2 are retained. Every target is now exactly the same fixed Euclidean ball.
-/

open Set Metric Manifold IsManifold Topology
open scoped ContDiff Manifold

noncomputable section
namespace GlobalEmbedding.Initialization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M]

/-- Native restriction to a coordinate ball already contained in the target. -/
def restrictChartTargetBall (e : OpenPartialHomeomorph M E) (ρ : ℝ)
    (hbuffer : closedBall (0 : E) ρ ⊆ e.target) : OpenPartialHomeomorph M E where
  toFun := e
  invFun := e.symm
  source := e.source ∩ e ⁻¹' ball 0 ρ
  target := ball 0 ρ
  map_source' := fun _ hx ↦ hx.2
  map_target' := by
    intro y hy
    have hyt := hbuffer (ball_subset_closedBall hy)
    exact ⟨e.map_target hyt, by simpa only [Set.mem_preimage, e.right_inv hyt] using hy⟩
  left_inv' := fun _ hx ↦ e.left_inv hx.1
  right_inv' := fun _ hy ↦ e.right_inv (hbuffer (ball_subset_closedBall hy))
  open_source := e.isOpen_inter_preimage isOpen_ball
  open_target := isOpen_ball
  continuousOn_toFun := e.continuousOn.mono inter_subset_left
  continuousOn_invFun := e.continuousOn_symm.mono (ball_subset_closedBall.trans hbuffer)

@[simp] theorem restrictChartTargetBall_apply (e : OpenPartialHomeomorph M E)
    (ρ : ℝ) (hb : closedBall (0 : E) ρ ⊆ e.target) (x : M) :
    restrictChartTargetBall e ρ hb x = e x := rfl

@[simp] theorem restrictChartTargetBall_symm_apply (e : OpenPartialHomeomorph M E)
    (ρ : ℝ) (hb : closedBall (0 : E) ρ ⊆ e.target) (y : E) :
    (restrictChartTargetBall e ρ hb).symm y = e.symm y := rfl

@[simp] theorem restrictChartTargetBall_source (e : OpenPartialHomeomorph M E)
    (ρ : ℝ) (hb : closedBall (0 : E) ρ ⊆ e.target) :
    (restrictChartTargetBall e ρ hb).source = e.source ∩ e ⁻¹' ball 0 ρ := rfl

@[simp] theorem restrictChartTargetBall_target (e : OpenPartialHomeomorph M E)
    (ρ : ℝ) (hb : closedBall (0 : E) ρ ⊆ e.target) :
    (restrictChartTargetBall e ρ hb).target = ball 0 ρ := rfl

theorem restrictChartTargetBall_mem_maximalAtlas [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (ρ : ℝ)
    (hb : closedBall (0 : E) ρ ⊆ e.target) :
    restrictChartTargetBall e ρ hb ∈ maximalAtlas 𝓘(ℝ, E) ∞ M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas he).mono inter_subset_left
  · exact (contMDiffOn_symm_of_mem_maximalAtlas he).mono (ball_subset_closedBall.trans hb)

variable {n : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

theorem ChartCutoffFamily.scaledAtlas_inner_coordinate_bound
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (i : Fin F.count) {x : M} (hx : x ∈ (F.scaledAtlas hT).inner i) :
    ‖(F.scaledAtlas hT).chart i x‖ < G.scaleRadius / 10 := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  change ‖rescaledChart _ _ T hTpos.ne' x‖ < _
  rw [norm_rescaledChart _ _ hTpos]
  have hd : dist (G.chart (F.parent i) x) (F.center i) < G.scaleRadius / (10 * T) := hx.2
  have hm := mul_lt_mul_of_pos_left hd hTpos
  have heq : T * (G.scaleRadius / (10 * T)) = G.scaleRadius / 10 := by field_simp
  exact heq ▸ hm

/-- The actual rescaled chart restricted to the fixed radius-ρ ball. -/
def ChartCutoffFamily.boundedChart {G : PreparedCharts M n} {T : ℝ}
    (F : ChartCutoffFamily G T) (hT : 1 ≤ T) (i : Fin F.count) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
  restrictChartTargetBall ((F.scaledAtlas hT).chart i) G.scaleRadius
    (rescaledChart_closedBall_buffer _ (G.radius_pos _) (G.scaleRadius_le _)
      (F.center_core i) (G.buffered _) hT)

/-- A native fixed-radius buffered atlas. The support graph is literally the
same graph as that of the previously constructed scale refinement. -/
def ChartCutoffFamily.boundedAtlas {G : PreparedCharts M n} {T : ℝ}
    (F : ChartCutoffFamily G T) (hT : 1 ≤ T) :
    GlobalEmbedding.Paper.BufferedAtlas M (EuclideanSpace ℝ (Fin n)) where
  count := F.count
  chart := F.boundedChart hT
  inner := F.innerDomain
  inner_open := (F.scaledAtlas hT).inner_open
  inner_subset := by
    intro i x hx
    refine ⟨hx.1, ?_⟩
    have hn := F.scaledAtlas_inner_coordinate_bound hT i hx
    change (F.scaledAtlas hT).chart i x ∈ ball 0 G.scaleRadius
    rw [mem_ball, dist_zero_right]
    linarith [G.scaleRadius_pos]
  cover := F.net_cover
  buffer := G.scaleRadius / 2
  buffer_pos := half_pos G.scaleRadius_pos
  buffered := by
    intro i x hx y hy
    have hn := F.scaledAtlas_inner_coordinate_bound hT i hx
    have hd : dist y ((F.scaledAtlas hT).chart i x) < G.scaleRadius / 2 := hy
    have ht := dist_triangle y ((F.scaledAtlas hT).chart i x) 0
    change dist y 0 < G.scaleRadius
    rw [dist_zero_right] at ht ⊢
    rw [dist_zero_right] at ht
    linarith [G.scaleRadius_pos]
  support := F.enlargedSupport

theorem ChartCutoffFamily.boundedAtlas_smooth
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T) :
    GlobalEmbedding.Paper.IsSmoothBufferedAtlas (F.boundedAtlas hT) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact restrictChartTargetBall_mem_maximalAtlas _ ((F.scaledAtlas_smooth hT).chart_mem i)
      G.scaleRadius (rescaledChart_closedBall_buffer _ (G.radius_pos _) (G.scaleRadius_le _)
        (F.center_core i) (G.buffered _) hT)
  · intro i x hx
    refine ⟨hx.1, ?_⟩
    have hn := F.scaledAtlas_support_coordinate_bound hT i hx
    change (F.scaledAtlas hT).chart i x ∈ ball 0 G.scaleRadius
    rw [mem_ball, dist_zero_right]
    linarith [G.scaleRadius_pos]

@[simp] theorem ChartCutoffFamily.boundedAtlas_target
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (i : Fin F.count) : ((F.boundedAtlas hT).chart i).target = ball 0 G.scaleRadius := rfl

@[simp] theorem ChartCutoffFamily.boundedAtlas_chart_apply
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (i : Fin F.count) (x : M) : (F.boundedAtlas hT).chart i x =
      T • (G.chart (F.parent i) x - F.center i) := rfl

@[simp] theorem ChartCutoffFamily.boundedAtlas_chart_symm_apply
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (i : Fin F.count) (y : EuclideanSpace ℝ (Fin n)) : ((F.boundedAtlas hT).chart i).symm y =
      (G.chart (F.parent i)).symm (T⁻¹ • y + F.center i) := rfl

theorem ChartCutoffFamily.boundedAtlas_supportDegree
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T) :
    (F.boundedAtlas hT).supportDegree = (F.scaledAtlas hT).supportDegree := rfl

/-- Every point in the entire fixed target ball pulls back to the interior of
the fixed compact parent core; this removes later derivative-domain premises. -/
theorem ChartCutoffFamily.scaledPoint_in_open_core
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (i : Fin F.count) {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ ball 0 G.scaleRadius) :
    F.center i + T⁻¹ • y ∈ ball (G.center (F.parent i)) (2 * G.radius (F.parent i)) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hnorm : ‖T⁻¹ • y‖ < G.scaleRadius := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hTpos)]
    apply lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hT))
    simpa only [mem_ball, dist_zero_right] using hy
  have hc : dist (F.center i) (G.center (F.parent i)) ≤ G.radius (F.parent i) := F.center_core i
  have hd : dist (F.center i + T⁻¹ • y) (F.center i) = ‖T⁻¹ • y‖ := by simp [dist_eq_norm]
  have ht := dist_triangle (F.center i + T⁻¹ • y) (F.center i) (G.center (F.parent i))
  rw [mem_ball]
  rw [hd] at ht
  linarith [G.scaleRadius_le (F.parent i)]

theorem ChartCutoffFamily.boundedAtlas_source_in_open_core
    {G : PreparedCharts M n} {T : ℝ} (F : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (i : Fin F.count) {x : M} (hx : x ∈ ((F.boundedAtlas hT).chart i).source) :
    G.chart (F.parent i) x ∈ ball (G.center (F.parent i)) (2 * G.radius (F.parent i)) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hball : (F.boundedAtlas hT).chart i x ∈ ball 0 G.scaleRadius := hx.2
  have hc := F.scaledPoint_in_open_core hT i hball
  simpa [smul_smul, hTpos.ne', add_comm] using hc

end GlobalEmbedding.Initialization
