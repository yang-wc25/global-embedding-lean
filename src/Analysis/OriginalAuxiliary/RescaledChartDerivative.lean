import Initialization.Geometry.RescaledMetricIdentity
import Initialization.Phase.NativeChartPhase
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Actual derivatives of the original rescaled charts

Source: `main.tex`, `prop:initialization`, the literal coordinate formula
`x = exp_p(y / T)`, and `thm:repair`'s original auxiliary tangent norm.

The fixed auxiliary norm is never changed. The actual forward derivative
acquires a factor `T`, and its squared operator norm acquires `T^2`.
These are equalities of the original objects, not additional bounds.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Initialization Manifold IsManifold Bundle
open scoped ContDiff
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace GlobalEmbedding.Continuation.OriginalAuxiliary

/-- Scalar homogeneity of the ordinary operator norm, for any fixed two
normed spaces. The later applications retain their supplied norm instances. -/
theorem auxiliary_operator_norm_smul {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : ℝ) (A : U →L[ℝ] V) : ‖t • A‖ = |t| * ‖A‖ := by
  rw [norm_smul, Real.norm_eq_abs]

section Algebraic

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Exact manifold chain rule for the same centered dilation chart. -/
theorem rescaledChart_forward_mfderiv
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (p : E) (T : ℝ) (hT : T ≠ 0) (x : M) (hx : x ∈ e.source) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (rescaledChart e p T hT) x =
      T • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x := by
  let a : E → E := fun y ↦ T • (y - p)
  have ha : HasFDerivAt a (T • ContinuousLinearMap.id ℝ E) (e x) :=
    ((hasFDerivAt_id (e x)).sub_const p).const_smul T
  have he' := (contMDiffAt_of_mem_maximalAtlas he hx).mdifferentiableAt (by simp)
  have h := mfderiv_comp x ha.differentiableAt.mdifferentiableAt he'
  rw [mfderiv_eq_fderiv, ha.fderiv] at h
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (rescaledChart e p T hT) x = _ at h
  exact h.trans (by ext v; rfl)

/-- The tangent equivalence used by the accepted initialization theorem
is the same scaled derivative, with the original tangent space as source. -/
theorem rescaledChart_tangentEquiv_apply
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (p : E) (T : ℝ) (hT : T ≠ 0) (x : M) (hx : x ∈ e.source)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    initializationChartTangentEquiv (rescaledChart e p T hT)
      (rescaledChart_mem_maximalAtlas e he p T hT) x hx v =
      T • initializationChartTangentEquiv e he x hx v := by
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (rescaledChart e p T hT) x v =
    T • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v
  rw [rescaledChart_forward_mfderiv e he p T hT x hx]
  rfl

/-- The inverse differential has the reciprocal factor at exactly the
same physical point. -/
theorem rescaledChart_inverse_mfderiv
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (p : E) (T : ℝ) (hT : T ≠ 0) (y : E)
    (hy : T⁻¹ • y + p ∈ e.target) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (rescaledChart e p T hT).symm y =
      T⁻¹ • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (T⁻¹ • y + p) := by
  ext v
  exact rescaledChart_inverse_mfderiv_apply e he p T hT hy v


end Algebraic

section Auxiliary

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)]
local notation "E" => EuclideanSpace ℝ (Fin n)

-- Specializing the original Euclidean coordinate model prevents its norm
-- instance from being reused for the distinct fixed auxiliary tangent norm.
attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
/-- The operator norm uses the original fixed auxiliary norm on the same
tangent space at `x`. No induced or rescaled norm is installed. -/
theorem rescaledChart_forward_norm
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (p : E) (T : ℝ) (hT : T ≠ 0) (x : M) (hx : x ∈ e.source) :
    ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (rescaledChart e p T hT) x :
      TangentSpace 𝓘(ℝ, E) x →L[ℝ] E)‖ =
      |T| * ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E)‖ := by
  let A : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x
  have hscale : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (rescaledChart e p T hT) x :
      TangentSpace 𝓘(ℝ, E) x →L[ℝ] E) = T • A :=
    rescaledChart_forward_mfderiv e he p T hT x hx
  have hnorm : ‖T • A‖ = |T| * ‖A‖ := auxiliary_operator_norm_smul T A
  exact (congrArg (fun L : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E ↦ ‖L‖) hscale).trans hnorm

attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
theorem rescaledChart_forward_norm_sq
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (p : E) (T : ℝ) (hT : T ≠ 0) (x : M) (hx : x ∈ e.source) :
    ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (rescaledChart e p T hT) x :
      TangentSpace 𝓘(ℝ, E) x →L[ℝ] E)‖^2 =
      T^2 * ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E)‖^2 := by
  rw [rescaledChart_forward_norm e he p T hT x hx, mul_pow, sq_abs]

attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
theorem rescaledChart_inverse_norm_sq
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (p : E) (T : ℝ) (hT : T ≠ 0) (y : E)
    (hy : T⁻¹ • y + p ∈ e.target) :
    ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (rescaledChart e p T hT).symm y :
      E →L[ℝ] TangentSpace 𝓘(ℝ, E) ((rescaledChart e p T hT).symm y))‖^2 =
      (T^2)⁻¹ * ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (T⁻¹ • y + p) :
      E →L[ℝ] TangentSpace 𝓘(ℝ, E) (e.symm (T⁻¹ • y + p)))‖^2 := by
  let A : E →L[ℝ] TangentSpace 𝓘(ℝ, E) (e.symm (T⁻¹ • y + p)) :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (T⁻¹ • y + p)
  have hscale : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (rescaledChart e p T hT).symm y :
      E →L[ℝ] TangentSpace 𝓘(ℝ, E) (e.symm (T⁻¹ • y + p))) = T⁻¹ • A :=
    rescaledChart_inverse_mfderiv e he p T hT y hy
  have hnorm : ‖T⁻¹ • A‖^2 = (T^2)⁻¹ * ‖A‖^2 := by
    rw [auxiliary_operator_norm_smul, mul_pow, sq_abs, inv_pow]
  exact (congrArg (fun L : E →L[ℝ] TangentSpace 𝓘(ℝ, E) (e.symm (T⁻¹ • y + p)) ↦
    ‖L‖^2) hscale).trans hnorm

end Auxiliary

end GlobalEmbedding.Continuation.OriginalAuxiliary

#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.rescaledChart_forward_mfderiv
#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.rescaledChart_forward_norm_sq
#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.rescaledChart_inverse_norm_sq
