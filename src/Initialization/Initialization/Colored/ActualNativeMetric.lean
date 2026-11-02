import Initialization.Colored.ActualMetricEstimate
import Initialization.Assembly.ChartImmersion

/-!
# Identification with the original native induced metric

This is an exact chart-chain-rule identity, including the native tangent-space
maps. Thus the operator field estimated in the colored approximation really is
the coordinate tensor of γ(H_(K,T)) − T²g for the same globally defined H.
-/

noncomputable section
open Set Function Metric Manifold IsManifold Bundle
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

section NativePullback

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {N : ℕ}

/-- The Gram of the actual coordinate derivative is exactly the pullback of
the original native inducedMetric, with its actual inverse-chart mfderiv. -/
theorem actualMetricOperator_native_pullback
    (H : M → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H)
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    {y : E} (hy : y ∈ e.target) (v w : E) :
    inner ℝ (actualMetricOperator (H ∘ e.symm) y v) w =
      inducedMetric (I := 𝓘(ℝ, E)) H (e.symm y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y w) := by
  rw [actualMetricOperator_inner,
    initialization_coordinate_fderiv_apply H hH e he hy v,
    initialization_coordinate_fderiv_apply H hH e he hy w, inducedMetric_apply]
  rfl

end NativePullback

section ColoredMetric

variable {n N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)

/-- Exact evaluation of the estimated operator as the original error tensor.
No auxiliary map or independently supplied tensor occurs on the right. -/
theorem metricInitializationMap_native_metric_error
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    {K T : ℝ} (hK : 1 ≤ K) (Q : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (p : Fin Q.count) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ ((Q.boundedAtlas hT).chart p).target) (v w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ
      ((actualMetricOperator
        (metricInitializationMap G g f S K T hK ∘ ((Q.boundedAtlas hT).chart p).symm) y -
          scaledTargetMetricOperator G g f Q p y) v) w =
      inducedMetric (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (metricInitializationMap G g f S K T hK) (((Q.boundedAtlas hT).chart p).symm y)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          ((Q.boundedAtlas hT).chart p).symm y v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          ((Q.boundedAtlas hT).chart p).symm y w) -
        T ^ 2 * g.inner (((Q.boundedAtlas hT).chart p).symm y)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            ((Q.boundedAtlas hT).chart p).symm y v)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            ((Q.boundedAtlas hT).chart p).symm y w) := by
  rw [ContinuousLinearMap.sub_apply, inner_sub_left,
    actualMetricOperator_native_pullback _
      (metricInitializationMap_contMDiff G g f S hS K T hK)
      ((Q.boundedAtlas hT).chart p) ((Q.boundedAtlas_smooth hT).chart_mem p) hy,
    scaledTargetMetricOperator_inner G g f Q hT p hy]

end ColoredMetric
end GlobalEmbedding.Initialization
