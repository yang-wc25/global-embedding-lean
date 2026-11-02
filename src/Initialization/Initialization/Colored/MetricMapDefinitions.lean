import Initialization.Colored.PreparedMap
import Initialization.Assembly.PreparedCoframeBounds
import GlobalEmbedding.Paper.Parallelizable

/-!
# Metric-generated actual initialization maps

The frozen coframe field is now produced from the original positive smooth
metric and full tangent frame. The compact-source construction below also
chooses the actual charts, palette and accepted whole-product selector internally.
It establishes the literal map, its smoothness and value bound; the higher
reference, metric-error and phase-margin conclusions remain separate obligations.
-/

noncomputable section
open Function Set Metric Manifold IsManifold Bundle
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

/-- No coframe field is an input: it is the actual positive-root normalized
coframe of g, expressed in the actual parent chart and frozen at each net center. -/
def metricInitializationMap (G : PreparedCharts M n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)
    {V : Type*} (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (K T : ℝ) (hK : 1 ≤ K) : M → V :=
  preparedInitializationMap G S (preparedCoframe G g f) K T hK

theorem metricInitializationMap_contMDiff (G : PreparedCharts M n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette)) 𝓘(ℝ, V) ∞ S)
    (K T : ℝ) (hK : 1 ≤ K) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞
      (metricInitializationMap G g f S K T hK) :=
  preparedInitializationMap_contMDiff G S hS (preparedCoframe G g f) K T hK

/-- The actual map has a zeroth-order reference bound chosen from the fixed
selector, before both real parameters, with no restriction on connectedness. -/
theorem exists_metricInitializationMap_value_bound (G : PreparedCharts M n)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V) (hS : Continuous S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀
      (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
      (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)
      (K T : ℝ) (hK : 1 ≤ K) (x : M),
      ‖metricInitializationMap G g f S K T hK x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_preparedInitializationMap_value_bound G S hS
  exact ⟨B, hB, fun g f K T hK x ↦ hb (preparedCoframe G g f) K T hK x⟩

end GlobalEmbedding.Initialization
