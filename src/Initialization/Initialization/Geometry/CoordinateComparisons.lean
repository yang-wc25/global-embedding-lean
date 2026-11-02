import Initialization.Geometry.PreparedCharts
import Initialization.Geometry.CoordinateExtensions

/-!
# Uniform genuine coordinate comparisons

Each fixed chart has a global smooth extension which equals that chart on its
two-radius core. Compactness and the mean value theorem give one comparison
constant for every pair of charts, before any net or frequency. In particular,
the connecting straight segment may leave the other chart: the globally smooth
extension makes the derivative estimate valid along the whole segment.
-/

open Set Metric Manifold IsManifold Topology
open scoped ContDiff Manifold

noncomputable section
namespace GlobalEmbedding.Initialization

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]

/-- The genuine fixed atlas supplies its own global coordinate extensions and
one positive cross-chart Lipschitz constant. No metric/volume/derivative bound
is an input. The empty atlas is retained by inserting 1 in the finite maximum. -/
theorem exists_prepared_coordinate_comparisons (G : PreparedCharts M n) :
    ∃ (F : Fin G.count → M → EuclideanSpace ℝ (Fin n)) (L : ℝ),
      1 ≤ L ∧
      (∀ j, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (F j)) ∧
      (∀ j x, x ∈ (G.chart j).source →
        G.chart j x ∈ closedBall (G.center j) (2 * G.radius j) → F j x = G.chart j x) ∧
      ∀ i j y z,
        y ∈ closedBall (G.center i) (2 * G.radius i) →
        z ∈ closedBall (G.center i) (2 * G.radius i) →
        dist (F j ((G.chart i).symm y)) (F j ((G.chart i).symm z)) ≤ L * dist y z := by
  classical
  have hcore (i : Fin G.count) :
      closedBall (G.center i) (2 * G.radius i) ⊆ (G.chart i).target :=
    (closedBall_subset_closedBall (by linarith [G.radius_pos i])).trans (G.buffered i)
  have extensions (j : Fin G.count) : ∃ f : M → EuclideanSpace ℝ (Fin n),
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f ∧
      ∀ x, x ∈ (G.chart j).source →
        G.chart j x ∈ closedBall (G.center j) (2 * G.radius j) → f x = G.chart j x := by
    let S := (G.chart j).symm '' closedBall (G.center j) (2 * G.radius j)
    have hS : IsCompact S := (isCompact_closedBall _ _).image_of_continuousOn
      ((G.chart j).continuousOn_symm.mono (hcore j))
    have hSe : S ⊆ (G.chart j).source := by
      rintro x ⟨y, hy, rfl⟩
      exact (G.chart j).map_target (hcore j hy)
    obtain ⟨f, hf, heq⟩ := exists_smooth_coordinate_extension
      (G.chart j) (G.chart_smooth j) hS hSe
    refine ⟨f, hf, ?_⟩
    intro x hxs hxc
    exact heq ⟨G.chart j x, hxc, (G.chart j).left_inv hxs⟩
  choose F hF hFeq using extensions
  have pairBounds (i j : Fin G.count) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y z, y ∈ closedBall (G.center i) (2 * G.radius i) →
        z ∈ closedBall (G.center i) (2 * G.radius i) →
        dist (F j ((G.chart i).symm y)) (F j ((G.chart i).symm z)) ≤ C * dist y z := by
    obtain ⟨B, hB, hbound⟩ := exists_coordinate_extension_pullback_bounds
      (F j) (hF j) (G.chart i) (G.chart_smooth i)
      (isCompact_closedBall (G.center i) (2 * G.radius i)) (hcore i)
    have hcoord : ContDiffOn ℝ ∞ (F j ∘ (G.chart i).symm) (G.chart i).target :=
      ((hF j).comp_contMDiffOn
        (contMDiffOn_symm_of_mem_maximalAtlas (G.chart_smooth i))).contDiffOn
    have hd (x : EuclideanSpace ℝ (Fin n))
        (hx : x ∈ closedBall (G.center i) (2 * G.radius i)) :
        DifferentiableAt ℝ (F j ∘ (G.chart i).symm) x :=
      (hcoord.contDiffAt ((G.chart i).open_target.mem_nhds (hcore i hx))).differentiableAt (by simp)
    have hb (x : EuclideanSpace ℝ (Fin n))
        (hx : x ∈ closedBall (G.center i) (2 * G.radius i)) :
        ‖fderiv ℝ (F j ∘ (G.chart i).symm) x‖ ≤ B 1 := by
      simpa only [norm_iteratedFDeriv_one] using hbound 1 x hx
    refine ⟨B 1, hB 1, ?_⟩
    intro y z hy hz
    simpa only [Function.comp_apply, dist_eq_norm] using
      (convex_closedBall (G.center i) (2 * G.radius i)).norm_image_sub_le_of_norm_fderiv_le
        hd hb hz hy
  choose C hC hCbound using pairBounds
  let bounds : Finset ℝ := insert 1 (Finset.univ.image (fun ij : Fin G.count × Fin G.count ↦ C ij.1 ij.2))
  have hbnonempty : bounds.Nonempty := by simp [bounds]
  let L := bounds.max' hbnonempty
  have hL : 1 ≤ L := Finset.le_max' bounds 1 (Finset.mem_insert_self _ _)
  have hCL (i j : Fin G.count) : C i j ≤ L :=
    Finset.le_max' bounds (C i j)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
  refine ⟨F, L, hL, hF, hFeq, ?_⟩
  intro i j y z hy hz
  exact (hCbound i j y z hy hz).trans
    (mul_le_mul_of_nonneg_right (hCL i j) dist_nonneg)

end GlobalEmbedding.Initialization
