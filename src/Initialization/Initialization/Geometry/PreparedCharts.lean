import Initialization.Geometry.ChartColoredCutoffs

/-!
# Internally prepared fixed charts and all-scale cutoffs

The preparation is chosen once from the original compact smooth manifold.
The radius and palette are fixed before either real frequency parameter.
No chart, geometric comparison, cutoff or uniform bound is an additional input
to the final existence theorem in this file.
-/

open Set Metric Manifold IsManifold Topology
open scoped ContDiff Manifold ENNReal

noncomputable section
namespace GlobalEmbedding.Initialization

open GlobalEmbedding.Offline

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

/-- Actual fixed charts with compact coordinate cores and one common positive
radius. This is construction data, produced below from compactness. -/
structure PreparedCharts (M : Type*) [TopologicalSpace M]
    (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] where
  count : ℕ
  chart : Fin count → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  center : Fin count → EuclideanSpace ℝ (Fin n)
  radius : Fin count → ℝ
  chart_smooth : ∀ i, chart i ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M
  radius_pos : ∀ i, 0 < radius i
  buffered : ∀ i, closedBall (center i) (4 * radius i) ⊆ (chart i).target
  cover : ∀ x : M, ∃ i, x ∈ (chart i).source ∧
    chart i x ∈ ball (center i) (radius i)
  scaleRadius : ℝ
  scaleRadius_pos : 0 < scaleRadius
  scaleRadius_le_one : scaleRadius ≤ 1
  scaleRadius_le : ∀ i, scaleRadius ≤ radius i

/-- Finite genuine chart preparation exists with no connectedness or
nonemptiness hypothesis. The inserted radius 1 handles an empty chart family. -/
theorem exists_preparedCharts [CompactSpace M] : Nonempty (PreparedCharts M n) := by
  classical
  obtain ⟨m, e, a, r, he, hr, hbuffer, hcover⟩ :=
    exists_finite_compact_chart_cover (E := EuclideanSpace ℝ (Fin n)) (M := M)
  let radii : Finset ℝ := insert 1 (Finset.univ.image r)
  have hrad : radii.Nonempty := by simp [radii]
  let ρ := radii.min' hrad
  have hρ : 0 < ρ := by
    have hmem : ρ ∈ radii := Finset.min'_mem radii hrad
    rcases Finset.mem_insert.mp hmem with h | h
    · simpa only [h] using (zero_lt_one : (0 : ℝ) < 1)
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact hi ▸ hr i
  exact ⟨{
    count := m
    chart := e
    center := a
    radius := r
    chart_smooth := he
    radius_pos := hr
    buffered := hbuffer
    cover := hcover
    scaleRadius := ρ
    scaleRadius_pos := hρ
    scaleRadius_le_one := Finset.min'_le radii 1 (Finset.mem_insert_self _ _)
    scaleRadius_le := fun i ↦ Finset.min'_le radii (r i)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)) }⟩

/-- The palette is fixed by the preparation, before K or T, and is at least 2. -/
def PreparedCharts.palette (G : PreparedCharts M n) : ℕ := G.count * (30 ^ n + 2) + 2

theorem PreparedCharts.palette_ge_two (G : PreparedCharts M n) : 2 ≤ G.palette := by
  simp [PreparedCharts.palette]

/-- Actual finite net centers and square-normalized cutoffs at one real scale.
The separation is retained for support-degree and scale-atlas consumers. -/
structure ChartCutoffFamily (G : PreparedCharts M n) (K : ℝ) where
  count : ℕ
  parent : Fin count → Fin G.count
  center : Fin count → EuclideanSpace ℝ (Fin n)
  color : Fin count → Fin G.palette
  cutoff : Fin count → M → ℝ
  center_core : ∀ i, center i ∈ closedBall (G.center (parent i)) (G.radius (parent i))
  separated : ∀ i j, i ≠ j → parent i = parent j →
    ENNReal.ofReal (G.scaleRadius / (10 * K)) ≤ edist (center i) (center j)
  net_cover : ∀ x : M, ∃ i, x ∈ (G.chart (parent i)).source ∧
    dist (G.chart (parent i) x) (center i) < G.scaleRadius / (10 * K)
  cutoff_eq : ∀ i, cutoff i = squareNormalizedCutoff
    (fun j ↦ scaledChartCutoff G.scaleRadius K
      (translatedChart (G.chart (parent j)) (center j))) i
  cutoff_smooth : ∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ (cutoff i)
  sum_sq : ∀ x, ∑ i, cutoff i x ^ 2 = 1
  support_subset : ∀ i, tsupport (cutoff i) ⊆ (G.chart (parent i)).source ∩
    (G.chart (parent i)) ⁻¹' closedBall (center i) (G.scaleRadius / (4 * K))
  same_color_disjoint : ∀ i j, i ≠ j → color i = color j →
    Disjoint (tsupport (cutoff i)) (tsupport (cutoff j))

/-- Construction at arbitrary real K, consuming only the internally prepared
fixed atlas. No geometric or analytic estimate is assumed. -/
theorem exists_chartCutoffFamily (G : PreparedCharts M n) {K : ℝ} (hK : 1 ≤ K) :
    Nonempty (ChartCutoffFamily G K) := by
  obtain ⟨N, parent, p, color, χ, hcore, hsep, hnet, hχ, hsmooth, hsquares, hsupp,
    hdisjoint⟩ := exists_fixedChart_colored_cutoffs_with_nets G.chart G.center G.radius
      G.chart_smooth G.radius_pos G.buffered G.cover G.scaleRadius_pos G.scaleRadius_le hK
  exact ⟨{
    count := N
    parent := parent
    center := p
    color := color
    cutoff := χ
    center_core := hcore
    separated := hsep
    net_cover := hnet
    cutoff_eq := hχ
    cutoff_smooth := hsmooth
    sum_sq := hsquares
    support_subset := hsupp
    same_color_disjoint := hdisjoint }⟩

/-- Full compact-source quantifier order: the actual chart preparation, common
radius and palette are fixed first; every real K ≥ 1 then has the actual family.
This is a geometry producer, not the complete colored approximation theorem. -/
theorem exists_compact_allScale_colored_cutoffs [CompactSpace M] :
    ∃ G : PreparedCharts M n, ∀ K : ℝ, 1 ≤ K → Nonempty (ChartCutoffFamily G K) := by
  obtain ⟨G⟩ := exists_preparedCharts (M := M) (n := n)
  exact ⟨G, fun _ hK ↦ exists_chartCutoffFamily G hK⟩

end GlobalEmbedding.Initialization
