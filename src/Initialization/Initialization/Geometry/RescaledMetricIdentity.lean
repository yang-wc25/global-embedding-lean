import Initialization.Geometry.BoundedScaledAtlas
import Initialization.Assembly.ChartCoframeNaturality

/-!
# Exact native metric identity in the actual rescaled charts

The tangent derivative is the native manifold derivative of the actual inverse
chart. The identity is with the original given metric g, scaled by T²; no
replacement metric or assumed coordinate derivative is introduced.
-/

open Set Metric Bundle Manifold IsManifold Topology Function
open scoped ContDiff Manifold

noncomputable section
namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

/-- The native tangent derivative of the exact inverse dilation chart. -/
theorem rescaledChart_inverse_mfderiv_apply
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (p : E) (T : ℝ) (hT : T ≠ 0) {y : E}
    (hy : T⁻¹ • y + p ∈ e.target) (v : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (rescaledChart e p T hT).symm y v =
      T⁻¹ • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (T⁻¹ • y + p) v := by
  let a : E → E := fun z ↦ T⁻¹ • z + p
  have ha : HasFDerivAt a (T⁻¹ • ContinuousLinearMap.id ℝ E) y := by
    simpa only [a, Pi.smul_apply, id_eq] using
      ((hasFDerivAt_id y).const_smul T⁻¹).add_const p
  have hma : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) a y := ha.differentiableAt.mdifferentiableAt
  have hderiv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) a y v = T⁻¹ • v := by
    rw [mfderiv_eq_fderiv, ha.fderiv]
    rfl
  have hc := congrArg (fun A ↦ A v) (mfderiv_comp y
    ((initialization_chart_mdifferentiable e he).mdifferentiableAt_symm hy) hma)
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e.symm ∘ a) y v =
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (a y)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) a y v) at hc
  rw [hderiv] at hc
  exact hc.trans ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (a y)).map_smul T⁻¹ v)

/-- The actual normalized coframe in a rescaled chart is exactly T⁻¹ times
its actual parent-coordinate value. -/
theorem chartOrthonormalCoframe_rescaled
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, E) (M := M) n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (p : E) (T : ℝ) (hT : T ≠ 0) {y : E}
    (hy : T⁻¹ • y + p ∈ e.target) :
    chartOrthonormalCoframe g f (rescaledChart e p T hT) y =
      T⁻¹ • chartOrthonormalCoframe g f e (T⁻¹ • y + p) := by
  apply ContinuousLinearMap.ext
  intro v
  change positiveRootCoframe 𝓘(ℝ, E) g f (e.symm (T⁻¹ • y + p))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (rescaledChart e p T hT).symm y v) = _
  rw [rescaledChart_inverse_mfderiv_apply e he p T hT hy v, map_smul]
  rfl

/-- The true Gram of the parent coefficient is exactly the coordinate matrix
of T²g under the native rescaled chart inverse. -/
theorem rescaledChart_coframe_gram_eq_scaled_metric
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, E) (M := M) n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (p : E) (T : ℝ) (hT : T ≠ 0) {y : E}
    (hy : T⁻¹ • y + p ∈ e.target) (v w : E) :
    inner ℝ (chartOrthonormalCoframe g f e (T⁻¹ • y + p) v)
      (chartOrthonormalCoframe g f e (T⁻¹ • y + p) w) =
      T ^ 2 * g.inner ((rescaledChart e p T hT).symm y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (rescaledChart e p T hT).symm y v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (rescaledChart e p T hT).symm y w) := by
  have hmetric := coordinateOrthonormalCoframe_metric 𝓘(ℝ, E) g f
    (rescaledChart e p T hT).symm y v w
  change inner ℝ (chartOrthonormalCoframe g f (rescaledChart e p T hT) y v)
    (chartOrthonormalCoframe g f (rescaledChart e p T hT) y w) = _ at hmetric
  rw [chartOrthonormalCoframe_rescaled g f e he p T hT hy] at hmetric
  rw [← hmetric]
  simp only [ContinuousLinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right]
  field_simp

end GlobalEmbedding.Initialization
