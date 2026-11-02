import Initialization.Colored.SmoothMap
import Initialization.Geometry.PreparedCharts

/-!
# The actual colored map from the internally prepared finite atlas

The finite charts, palette, real-scale nets, square-normalized cutoffs and
same-color support separation are supplied by the actual compact-source
producer. The phase is the frozen coordinate coframe applied to chart(x)-p;
the real frequency T occurs exactly once, inside the exponential.
-/

noncomputable section
open Function Set Metric Manifold IsManifold
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

instance preparedPalette_positive (G : PreparedCharts M n) : Fact (0 < G.palette) :=
  ⟨lt_of_lt_of_le (by decide : 0 < 2) G.palette_ge_two⟩

/-- The literal frozen linear phase in the actual parent chart. It is defined
everywhere, but only its germ on the cutoff support is used for smoothness. -/
def preparedFrozenPhase {G : PreparedCharts M n} {K : ℝ} (F : ChartCutoffFamily G K)
    (Θ : Fin G.count → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (l : Fin n) (i : Fin F.count) (x : M) : ℝ :=
  (Θ (F.parent i) (F.center i) (G.chart (F.parent i) x - F.center i)) l

/-- The support inclusion produced from the actual geometry proves the
smoothness needed by the zero-extension construction, including boundaries. -/
theorem preparedFrozenPhase_contMDiffAt {G : PreparedCharts M n} {K : ℝ}
    (F : ChartCutoffFamily G K)
    (Θ : Fin G.count → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (l : Fin n) (i : Fin F.count) (x : M) (hx : x ∈ tsupport (F.cutoff i)) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞
      (preparedFrozenPhase F Θ l i) x := by
  have hchart := contMDiffAt_of_mem_maximalAtlas (G.chart_smooth (F.parent i))
    (F.support_subset i hx).1
  have hlinear : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞
      ((EuclideanSpace.proj l).comp (Θ (F.parent i) (F.center i))) :=
    ((EuclideanSpace.proj l).comp (Θ (F.parent i) (F.center i))).contDiff.contMDiff
  exact hlinear.contMDiffAt.comp x (hchart.sub contMDiffAt_const)

/-- The genuine whole-product sphere map built from the real net at scale K. -/
def preparedColoredProduct {G : PreparedCharts M n} {K : ℝ} (F : ChartCutoffFamily G K)
    (Θ : Fin G.count → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (T : ℝ) : M → FreeHopfProduct (fun _ : Fin n ↦ G.palette) :=
  coloredProduct F.color F.cutoff (preparedFrozenPhase F Θ)
    F.same_color_disjoint F.sum_sq T

theorem preparedColoredProduct_contMDiff {G : PreparedCharts M n} {K : ℝ}
    (F : ChartCutoffFamily G K)
    (Θ : Fin G.count → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (T : ℝ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (freeHopfModel (fun _ : Fin n ↦ G.palette)) ∞ (preparedColoredProduct F Θ T) :=
  coloredProduct_contMDiff F.color F.cutoff (preparedFrozenPhase F Θ)
    F.same_color_disjoint F.sum_sq T F.cutoff_smooth (preparedFrozenPhase_contMDiffAt F Θ)

/-- Formula (7.2) holds literally in the native complex coordinates. -/
theorem preparedColoredProduct_coordinate {G : PreparedCharts M n} {K : ℝ}
    (F : ChartCutoffFamily G K)
    (Θ : Fin G.count → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (T : ℝ) (x : M) (l : Fin n) (c : Fin G.palette) :
    ((preparedColoredProduct F Θ T x l : PlanarHopfAmbient G.palette) c) =
      ∑ i, if F.color i = c then F.cutoff i x •
        (Circle.exp (2 * Real.pi * T *
          (Θ (F.parent i) (F.center i) (G.chart (F.parent i) x - F.center i)) l) : ℂ)
        else 0 := rfl

/-- H is the same actual selector evaluated on the constructed sphere map. -/
def preparedSelectorMap {G : PreparedCharts M n} {K : ℝ} {V : Type*}
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (F : ChartCutoffFamily G K)
    (Θ : Fin G.count → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (T : ℝ) : M → V :=
  S ∘ preparedColoredProduct F Θ T

theorem preparedSelectorMap_contMDiff {G : PreparedCharts M n} {K : ℝ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette)) 𝓘(ℝ, V) ∞ S)
    (F : ChartCutoffFamily G K)
    (Θ : Fin G.count → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (T : ℝ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞ (preparedSelectorMap S F Θ T) :=
  hS.comp (preparedColoredProduct_contMDiff F Θ T)

/-- The net and cutoff choice depends on K alone, so varying T keeps the same
actual colored family. The input preparation was already fixed before K. -/
def preparedCutoffsAt (G : PreparedCharts M n) (K : ℝ) (hK : 1 ≤ K) :
    ChartCutoffFamily G K :=
  Classical.choice (exists_chartCutoffFamily G hK)

/-- The actual all-scale initialization map, with both original parameters real. -/
def preparedInitializationMap (G : PreparedCharts M n) {V : Type*}
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (Θ : Fin G.count → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (K T : ℝ) (hK : 1 ≤ K) : M → V :=
  preparedSelectorMap S (preparedCutoffsAt G K hK) Θ T

theorem preparedInitializationMap_contMDiff (G : PreparedCharts M n)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette)) 𝓘(ℝ, V) ∞ S)
    (Θ : Fin G.count → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (K T : ℝ) (hK : 1 ≤ K) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞
      (preparedInitializationMap G S Θ K T hK) :=
  preparedSelectorMap_contMDiff S hS (preparedCutoffsAt G K hK) Θ T

/-- The value bound comes only from the fixed selector and is chosen before
the real scales, every net size, and the frozen coframe coefficients. -/
theorem exists_preparedInitializationMap_value_bound (G : PreparedCharts M n)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V) (hS : Continuous S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀
      (Θ : Fin G.count → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (K T : ℝ) (hK : 1 ≤ K) (x : M),
      ‖preparedInitializationMap G S Θ K T hK x‖ ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.bddAbove_image hS.norm.continuousOn
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro Θ K T hK x
  exact (hB (Set.mem_image_of_mem _ (Set.mem_univ _))).trans (le_max_right _ _)

end GlobalEmbedding.Initialization
