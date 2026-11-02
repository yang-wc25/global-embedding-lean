import Initialization.Assembly.ChartCoframeEquiv
import Initialization.Geometry.PreparedCharts

/-!
# Metric-generated uniform coframe budgets on the actual prepared charts

All constants are produced from the given metric, its actual normalized frame,
and the compact cores of the fixed finite preparation. They precede K and T.
This includes a uniform inverse bound; it is not a hypothesis of the producer.
-/

noncomputable section
open Bundle Manifold Set Metric IsManifold
open scoped ContDiff

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

abbrev preparedCoframe
    (G : PreparedCharts M n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)
    (i : Fin G.count) := chartOrthonormalCoframe g f (G.chart i)

/-- One fixed positive derivative sequence and one fixed inverse bound control
every genuine coefficient field on every 4r buffered compact core. Finite empty
preparations are handled by the added constant 1. -/
theorem exists_preparedCoframe_uniform_bounds
    (G : PreparedCharts M n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n) :
    ∃ (B : ℕ → ℝ) (L : ℝ),
      (∀ j, 1 ≤ B j) ∧ 1 ≤ L ∧
      (∀ j i y, y ∈ closedBall (G.center i) (4 * G.radius i) →
        ‖iteratedFDeriv ℝ j (preparedCoframe G g f i) y‖ ≤ B j) ∧
      (∀ i y (hy : y ∈ closedBall (G.center i) (4 * G.radius i)),
        ‖((chartOrthonormalCoframeEquiv g f (G.chart i) (G.chart_smooth i) y
          (G.buffered i hy)).symm :
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ L) := by
  classical
  have each (i : Fin G.count) := exists_chartOrthonormalCoframe_bounds g f (G.chart i)
    (G.chart_smooth i) (isCompact_closedBall (G.center i) (4 * G.radius i)) (G.buffered i)
  choose B L hB hL hderiv hinverse using each
  refine ⟨fun j ↦ 1 + ∑ i, B i j, 1 + ∑ i, L i, ?_, ?_, ?_, ?_⟩
  · intro j
    have : 0 ≤ ∑ i, B i j := Finset.sum_nonneg fun i _ ↦ (hB i j).le
    linarith
  · have : 0 ≤ ∑ i, L i := Finset.sum_nonneg fun i _ ↦ (hL i).le
    linarith
  · intro j i y hy
    have hb : B i j ≤ ∑ i, B i j :=
      Finset.single_le_sum (fun i _ ↦ (hB i j).le) (Finset.mem_univ i)
    exact (hderiv i j y hy).trans (by linarith)
  · intro i y hy
    have hl : L i ≤ ∑ i, L i :=
      Finset.single_le_sum (fun i _ ↦ (hL i).le) (Finset.mem_univ i)
    exact (hinverse i y hy).trans (by linarith)

/-- The same actual inverse budget gives the uniform elliptic lower estimate.
The norm is the original coordinate Euclidean norm, without replacement. -/
theorem chartOrthonormalCoframe_ellipticity
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ e.target)
    (L : ℝ)
    (hL : ‖((chartOrthonormalCoframeEquiv g f e he y hy).symm :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ L)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖v‖ ≤ L * ‖chartOrthonormalCoframe g f e y v‖ := by
  let c := chartOrthonormalCoframeEquiv g f e he y hy
  calc
    ‖v‖ = ‖c.symm (c v)‖ := by rw [c.symm_apply_apply]
    _ ≤ ‖(c.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ *
        ‖c v‖ := (c.symm : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)).le_opNorm (c v)
    _ ≤ L * ‖chartOrthonormalCoframe g f e y v‖ :=
      mul_le_mul_of_nonneg_right hL (norm_nonneg _)

end GlobalEmbedding.Initialization
