import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The metric induced by a map into Euclidean space

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition
`defn:phase`, lines 200–205. The differential `mfderiv` is defined for every map (and is zero
where the map is not differentiable), so the pointwise pullback below is defined without a
differentiability hypothesis. For a differentiable immersion, injectivity of the differential
makes this form positive definite. For an arbitrary map it is only positive semidefinite and can
be degenerate; a constant map induces the zero form.

This is a pointwise family of bilinear forms. It does not assert that the family is a smooth
section of a tensor bundle.
-/

noncomputable section

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The pointwise pullback of the Euclidean inner product by the manifold differential of `F`.

For `F : M → ℝ^N`, this is `γ(F)_x(v,w) = ⟪dF_x(v), dF_x(w)⟫`. The definition uses the total
manifold derivative, which is zero at points where `F` is not differentiable. Positivity for
immersions is a separate consequence of differentiability and injectivity of that derivative.
Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`, lines
200–205.
-/
def inducedMetric {N : ℕ} (F : M → EuclideanSpace ℝ (Fin N)) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) :=
  let D :=
    (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x)
  LinearMap.BilinForm.comp (innerₗ (EuclideanSpace ℝ (Fin N)))
    D.toLinearMap D.toLinearMap

/-- Evaluation of the induced metric is the Euclidean inner product of the two differentials.
Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`, lines
200–205.
-/
@[simp]
theorem inducedMetric_apply {N : ℕ} (F : M → EuclideanSpace ℝ (Fin N)) (x : M)
    (v w : TangentSpace I x) :
    inducedMetric F x v w =
      innerₗ (EuclideanSpace ℝ (Fin N))
        (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x)
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x v))
        (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x)
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x w)) := rfl

/-- The induced form is positive semidefinite for every map, including maps that are not
differentiable at `x`. -/
theorem inducedMetric_isPosSemidef {N : ℕ} (F : M → EuclideanSpace ℝ (Fin N)) (x : M) :
    (inducedMetric (I := I) F x).IsPosSemidef := by
  rw [LinearMap.BilinForm.isPosSemidef_def]
  constructor
  · rw [LinearMap.BilinForm.isSymm_def]
    intro v w
    simp only [inducedMetric_apply, innerₗ_apply_apply]
    exact real_inner_comm
      ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x))
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x w))
      ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x))
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x v))
  · rw [LinearMap.BilinForm.isNonneg_def]
    intro v
    simp only [inducedMetric_apply, innerₗ_apply_apply]
    exact real_inner_self_nonneg (x :=
      (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x))
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x v))

/-- If the manifold differential is injective, the induced form is positive definite on nonzero
tangent vectors. In particular this applies at differentiability points of an immersion, where
injectivity of the differential is the immersion condition. -/
theorem inducedMetric_pos_of_injective_mfderiv {N : ℕ}
    (F : M → EuclideanSpace ℝ (Fin N)) (x : M)
    (hD : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x))
    {v : TangentSpace I x} (hv : v ≠ 0) :
    0 < inducedMetric F x v v := by
  rw [inducedMetric_apply, innerₗ_apply_apply, real_inner_self_pos]
  intro h
  have hzero : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x v = 0 :=
    (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x)).injective (by simpa using h)
  exact hv (hD (by simpa using hzero))

end GlobalEmbedding.Paper
