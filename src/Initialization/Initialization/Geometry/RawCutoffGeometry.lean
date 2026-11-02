import Initialization.Geometry.UniformSupportDegree
import GlobalEmbedding.Offline.BoundedSquareCutoffSum

/-! Literal raw cutoffs, plateau coverage and internally proved multiplicity. -/

open Set Metric Filter Manifold IsManifold Topology
open scoped ContDiff Manifold

noncomputable section
namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Offline

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

def ChartCutoffFamily.rawCutoff {G : PreparedCharts M n} {K : ℝ}
    (F : ChartCutoffFamily G K) (i : Fin F.count) : M → ℝ :=
  scaledChartCutoff G.scaleRadius K (translatedChart (G.chart (F.parent i)) (F.center i))

theorem ChartCutoffFamily.rawCutoff_buffer {G : PreparedCharts M n} {K : ℝ}
    (F : ChartCutoffFamily G K) (i : Fin F.count) :
    closedBall (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius ⊆
      (translatedChart (G.chart (F.parent i)) (F.center i)).target :=
  translatedChart_closedBall_buffer _ (G.radius_pos _) (G.scaleRadius_le _)
    (F.center_core i) (G.buffered _)

theorem ChartCutoffFamily.rawCutoff_smooth {G : PreparedCharts M n} {K : ℝ}
    (F : ChartCutoffFamily G K) (hK : 1 ≤ K) (i : Fin F.count) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ (F.rawCutoff i) :=
  scaledChartCutoff_contMDiff _ _ G.scaleRadius_pos hK _
    (translatedChart_mem_maximalAtlas _ (G.chart_smooth _) _) (F.rawCutoff_buffer i)

theorem ChartCutoffFamily.rawCutoff_support_subset {G : PreparedCharts M n} {K : ℝ}
    (F : ChartCutoffFamily G K) (hK : 1 ≤ K) (i : Fin F.count) :
    tsupport (F.rawCutoff i) ⊆ F.enlargedSupport i := by
  intro x hx
  have hs := (scaledChartCutoff_support_buffers G.scaleRadius K G.scaleRadius_pos hK
    (translatedChart (G.chart (F.parent i)) (F.center i)) (F.rawCutoff_buffer i)).2.2.2 hx
  refine ⟨hs.1, ?_⟩
  have hd : dist (G.chart (F.parent i) x) (F.center i) < G.scaleRadius / (4 * K) := by
    simpa only [Set.mem_preimage, translatedChart_apply, mem_ball, dist_zero_right,
      dist_eq_norm, sub_zero] using hs.2
  exact hd.le

theorem ChartCutoffFamily.rawCutoff_plateau_cover {G : PreparedCharts M n} {K : ℝ}
    (F : ChartCutoffFamily G K) (hK : 1 ≤ K) (x : M) :
    ∃ i, F.rawCutoff i x = 1 := by
  obtain ⟨i, hxs, hdist⟩ := F.net_cover x
  refine ⟨i, ?_⟩
  apply scaledChartCutoff_one G.scaleRadius K G.scaleRadius_pos hK
    (translatedChart (G.chart (F.parent i)) (F.center i))
  refine ⟨hxs, ?_⟩
  simpa only [Set.mem_preimage, translatedChart_apply, mem_closedBall, dist_zero_right,
    dist_eq_norm, sub_zero] using hdist.le

theorem ChartCutoffFamily.rawCutoff_squareSum_ge_one {G : PreparedCharts M n} {K : ℝ}
    (F : ChartCutoffFamily G K) (hK : 1 ≤ K) (x : M) :
    1 ≤ squareCutoffSum F.rawCutoff x :=
  one_le_squareCutoffSum_of_plateau _ _ (F.rawCutoff_plateau_cover hK x)

theorem ChartCutoffFamily.cutoff_eq_normalized_raw {G : PreparedCharts M n} {K : ℝ}
    (F : ChartCutoffFamily G K) (i : Fin F.count) :
    F.cutoff i = squareNormalizedCutoff F.rawCutoff i := F.cutoff_eq i

/-- Every raw support through a point is either a chosen active index or an
actual neighbor of that index. Thus graph degree gives true local multiplicity. -/
theorem ChartCutoffFamily.rawCutoff_multiplicity_of_degree
    {G : PreparedCharts M n} {K : ℝ} (F : ChartCutoffFamily G K) (hK : 1 ≤ K)
    {D : ℕ} (hD : (F.scaledAtlas hK).supportDegree ≤ D) (x : M) :
    (activeCutoffIndices F.rawCutoff x).card ≤ D + 1 := by
  classical
  obtain ⟨i, hi⟩ := F.rawCutoff_plateau_cover hK x
  have hix : x ∈ tsupport (F.rawCutoff i) := subset_tsupport _ (by simp [Function.mem_support, hi])
  have hsup : activeCutoffIndices F.rawCutoff x ⊆
      insert i ((F.scaledAtlas hK).supportGraph.neighborFinset i) := by
    intro j hj
    by_cases hij : j = i
    · exact Finset.mem_insert.mpr (Or.inl hij)
    · apply Finset.mem_insert_of_mem
      apply ((F.scaledAtlas hK).supportGraph.mem_neighborFinset i j).mpr
      refine ⟨(fun h ↦ hij h.symm), x, F.rawCutoff_support_subset hK i hix, ?_⟩
      exact F.rawCutoff_support_subset hK j ((mem_activeCutoffIndices _ _ _).mp hj)
  have hdegree : (F.scaledAtlas hK).supportGraph.degree i ≤ D := by
    apply le_trans ?_ hD
    exact Finset.le_sup (f := fun i ↦ (F.scaledAtlas hK).supportGraph.degree i) (Finset.mem_univ i)
  calc
    (activeCutoffIndices F.rawCutoff x).card ≤
        (insert i ((F.scaledAtlas hK).supportGraph.neighborFinset i)).card := Finset.card_le_card hsup
    _ ≤ ((F.scaledAtlas hK).supportGraph.neighborFinset i).card + 1 := Finset.card_insert_le _ _
    _ ≤ D + 1 := Nat.add_le_add_right hdegree 1

/-- Compactness supplies the multiplicity bound before every real scale. -/
theorem exists_uniform_rawCutoff_multiplicity [CompactSpace M] (G : PreparedCharts M n) :
    ∃ D : ℕ, ∀ K : ℝ, ∀ hK : 1 ≤ K, ∀ F : ChartCutoffFamily G K,
      ∀ x, (activeCutoffIndices F.rawCutoff x).card ≤ D := by
  obtain ⟨D, hD⟩ := exists_uniform_enlargedSupport_degree G
  exact ⟨D + 1, fun K hK F x ↦ F.rawCutoff_multiplicity_of_degree hK (hD K hK F) x⟩

end GlobalEmbedding.Initialization
