import Initialization.Geometry.ScaledBufferedAtlas
import Initialization.Geometry.CoordinateComparisons
import Initialization.Geometry.EuclideanPackingRatio
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Uniform degree of the actual enlarged-support graph

This is a graph-degree bound, not just a pointwise overlap estimate. For every
fixed parent chart, all neighboring centers lie in one coordinate-extension
image ball. Actual Euclidean volume bounds that entire set; summing over the
fixed parent chart count gives a uniform degree before choosing the scale.
-/

open Set Metric Manifold IsManifold Topology
open scoped ContDiff Manifold ENNReal

noncomputable section
namespace GlobalEmbedding.Initialization

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]

/-- A genuine uniform graph-degree bound for every actual scale refinement of
the fixed preparation. It is produced from compactness and Euclidean volume;
no support degree, volume comparison or Lipschitz constant is an input. -/
theorem exists_uniform_enlargedSupport_degree (G : PreparedCharts M n) :
    ∃ D : ℕ, ∀ T : ℝ, ∀ hT : 1 ≤ T, ∀ F : ChartCutoffFamily G T,
      (F.scaledAtlas hT).supportDegree ≤ D := by
  classical
  obtain ⟨ext, L, hL, _hextsmooth, hext, hcomparison⟩ :=
    exists_prepared_coordinate_comparisons G
  let A : ℝ := 10 * (L + 1)
  let B : ℕ := ⌈(3 * (A + 1)) ^ n⌉₊
  refine ⟨G.count * B, ?_⟩
  intro T hT F
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  let δ := G.scaleRadius / (10 * T)
  have hδ : 0 < δ := div_pos G.scaleRadius_pos (by positivity)
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hpoint (i : Fin F.count) (j : Fin G.count) (v : Fin F.count)
      (hp : F.parent v = j)
      (hinter : (F.enlargedSupport i ∩ F.enlargedSupport v).Nonempty) :
      edist (F.center v) (ext j ((G.chart (F.parent i)).symm (F.center i))) ≤
        ENNReal.ofReal (A * δ) := by
    obtain ⟨x, hxi, hxv⟩ := hinter
    have hy : G.chart (F.parent i) x ∈
        closedBall (G.center (F.parent i)) (2 * G.radius (F.parent i)) :=
      F.enlargedSupport_in_core hT i hxi
    have hpcenter : F.center i ∈
        closedBall (G.center (F.parent i)) (2 * G.radius (F.parent i)) :=
      (closedBall_subset_closedBall (by linarith [G.radius_pos (F.parent i)])) (F.center_core i)
    have hextx : ext j x = G.chart j x := by
      apply hext j x
      · simpa only [hp] using hxv.1
      · simpa only [hp] using F.enlargedSupport_in_core hT v hxv
    have hcomp := hcomparison (F.parent i) j (G.chart (F.parent i) x) (F.center i) hy hpcenter
    rw [(G.chart (F.parent i)).left_inv hxi.1] at hcomp
    have hv : dist (F.center v) (ext j x) ≤ G.scaleRadius / (4 * T) := by
      rw [hextx]
      simpa only [hp, Set.mem_preimage, Metric.mem_closedBall, dist_comm] using hxv.2
    have hi : dist (G.chart (F.parent i) x) (F.center i) ≤ G.scaleRadius / (4 * T) := hxi.2
    have hcomp' : dist (ext j x) (ext j ((G.chart (F.parent i)).symm (F.center i))) ≤
        L * (G.scaleRadius / (4 * T)) :=
      hcomp.trans (mul_le_mul_of_nonneg_left hi (by linarith))
    have hd : dist (F.center v) (ext j ((G.chart (F.parent i)).symm (F.center i))) ≤
        A * δ := by
      have ht := dist_triangle (F.center v) (ext j x)
        (ext j ((G.chart (F.parent i)).symm (F.center i)))
      have heq : A * δ = (L + 1) * (G.scaleRadius / T) := by dsimp [A, δ]; ring
      rw [heq]
      have hrnonneg : 0 ≤ G.scaleRadius / T := div_nonneg G.scaleRadius_pos.le hTpos.le
      have hquarter : G.scaleRadius / (4 * T) = (G.scaleRadius / T) / 4 := by ring
      rw [hquarter] at hv hcomp'
      nlinarith
    simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hd
  have hdegree (i : Fin F.count) : (F.scaledAtlas hT).supportGraph.degree i ≤ G.count * B := by
    let s := (F.scaledAtlas hT).supportGraph.neighborFinset i
    have hfiber (j : Fin G.count) : (s.filter (fun v ↦ F.parent v = j)).card ≤ B := by
      apply euclidean_packing_card_le (s.filter (fun v ↦ F.parent v = j)) F.center
        (ext j ((G.chart (F.parent i)).symm (F.center i))) hδ hA
      · intro v hv w hw hvw
        exact F.separated v w hvw ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm)
      · intro v hv
        have hmem := (Finset.mem_filter.mp hv).1
        have hp := (Finset.mem_filter.mp hv).2
        have hadj : (F.scaledAtlas hT).supportGraph.Adj i v := by
          exact ((F.scaledAtlas hT).supportGraph.mem_neighborFinset i v).mp hmem
        exact hpoint i j v hp hadj.2
    have hsum : s.card = ∑ j : Fin G.count, (s.filter (fun v ↦ F.parent v = j)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)
    calc
      (F.scaledAtlas hT).supportGraph.degree i = s.card := by rfl
      _ = ∑ j : Fin G.count, (s.filter (fun v ↦ F.parent v = j)).card := hsum
      _ ≤ ∑ _j : Fin G.count, B := Finset.sum_le_sum (fun j _ ↦ hfiber j)
      _ = G.count * B := by simp
  unfold GlobalEmbedding.Paper.BufferedAtlas.supportDegree
  exact Finset.sup_le (fun i _ ↦ hdegree i)

/-- The fixed preparation, reference buffer and graph-degree bound are chosen
before all scales. The resulting atlas is an actual native smooth buffered atlas. -/
theorem exists_compact_allScale_atlases_uniform_degree :
    ∃ (G : PreparedCharts M n) (D : ℕ), ∀ T : ℝ, ∀ hT : 1 ≤ T,
      ∃ F : ChartCutoffFamily G T,
        GlobalEmbedding.Paper.IsSmoothBufferedAtlas (F.scaledAtlas hT) ∧
        (∀ i, IsCompact ((F.scaledAtlas hT).support i)) ∧
        (F.scaledAtlas hT).buffer = G.scaleRadius / 2 ∧
        (F.scaledAtlas hT).supportDegree ≤ D := by
  obtain ⟨G⟩ := exists_preparedCharts (M := M) (n := n)
  obtain ⟨D, hD⟩ := exists_uniform_enlargedSupport_degree G
  refine ⟨G, D, ?_⟩
  intro T hT
  obtain ⟨F⟩ := exists_chartCutoffFamily G hT
  exact ⟨F, F.scaledAtlas_smooth hT, F.enlargedSupport_compact hT, rfl, hD T hT F⟩

end GlobalEmbedding.Initialization
