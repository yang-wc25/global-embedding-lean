import Initialization.Assembly.AtlasCjNorm
import Initialization.Colored.ActualMetricEstimate

/-!
# Rescaled Fréchet atlas norms for the one actual initialization map

The atlas is the actual T-scale bounded atlas. The map is the actual global
metricInitializationMap. The reference tensor is the exact pullback of T²g.
Taking the finite maximum of chart norms preserves every bound, including the
case of an empty atlas. All output sequences precede K and T.
-/

noncomputable section
open Bundle Manifold Set Metric IsManifold
open scoped ContDiff

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

def initializationAtlas (G : PreparedCharts M n) (T : ℝ) (hT : 1 ≤ T) :
    BufferedAtlas M (EuclideanSpace ℝ (Fin n)) :=
  (preparedCutoffsAt G T hT).boundedAtlas hT

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def initializationMapRescaledCjNorm
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (j : ℕ) (K T : ℝ) (hK : 1 ≤ K) (hT : 1 ≤ T) : ℝ :=
  finiteAtlasCjNorm j
    (fun p : Fin (initializationAtlas G T hT).count ↦
      metricInitializationMap G g f S K T hK ∘ ((initializationAtlas G T hT).chart p).symm)
    (fun p ↦ ((initializationAtlas G T hT).chart p).target)

/-- Every reference C^j norm of the actual global H is uniformly bounded in
the actual scaled atlas, with no dependence on its increasing chart count. -/
theorem exists_initializationMap_reference_norm_bounds [CompactSpace M]
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette)) 𝓘(ℝ, V) ∞ S) :
    ∃ R : ℕ → ℝ, (∀ j, 0 < R j) ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T) (j : ℕ),
        initializationMapRescaledCjNorm G g f S j K T hK (hK.trans hKT) ≤ R j := by
  obtain ⟨R, _A, hR, _hA, hbound⟩ := exists_actualSelectedSource_jet_bounds G g f S hS
  refine ⟨fun j ↦ 1 + ∑ k ∈ Finset.range (j+1), R k, ?_, ?_⟩
  · intro j
    have hsum : 0 ≤ ∑ k ∈ Finset.range (j+1), R k :=
      Finset.sum_nonneg (fun k _ ↦ (hR k).le)
    linarith
  · intro K T hK hKT j
    apply le_trans (finiteAtlasCjNorm_le_sum_of_jet_bounds j _ _ R (fun k ↦ (hR k).le) ?_)
    · linarith
    · intro p k _hk y hy
      exact ((hbound K T hK hKT (preparedCutoffsAt G K hK)
        (preparedCutoffsAt G T (hK.trans hKT)) p k).1 y hy).1

/-- The literal coefficient defect of γ(H)-T²g in the actual T-scale chart. -/
def initializationMetricDefect
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (K T : ℝ) (hK : 1 ≤ K) (hT : 1 ≤ T)
    (p : Fin (initializationAtlas G T hT).count) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  actualMetricOperator
    (metricInitializationMap G g f S K T hK ∘ ((initializationAtlas G T hT).chart p).symm) y -
    scaledTargetMetricOperator G g f (preparedCutoffsAt G T hT) p y

def initializationMetricRescaledCjNorm
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (j : ℕ) (K T : ℝ) (hK : 1 ≤ K) (hT : 1 ≤ T) : ℝ :=
  finiteAtlasCjNorm j (initializationMetricDefect G g f S K T hK hT)
    (fun p ↦ ((initializationAtlas G T hT).chart p).target)

/-- Equation (7.1) in the Fréchet maximum-over-charts norm, for every fixed
order and all real T≥K≥1. The constants are generated before both frequencies. -/
theorem exists_initializationMetric_error_norm_bounds [CompactSpace M]
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette)) 𝓘(ℝ, V) ∞ S)
    (hGram : ∀ z, Matrix.gram ℝ
      (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ G.palette) l S z) = 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T) (j : ℕ),
        initializationMetricRescaledCjNorm G g f S j K T hK (hK.trans hKT) ≤
          C j * (K⁻¹ + K / T) := by
  obtain ⟨C, hC, hbound⟩ := exists_metricInitializationMap_cj_bounds G g f S hS hGram
  refine ⟨C, hC, ?_⟩
  intro K T hK hKT j
  apply finiteAtlasCjNorm_le
  · exact mul_nonneg (hC j).le ((initialization_error_scale_bounds hK hKT).2.2.1)
  · intro p
    exact hbound K T hK hKT (preparedCutoffsAt G T (hK.trans hKT)) p j

end GlobalEmbedding.Initialization
