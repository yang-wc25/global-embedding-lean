import GlobalEmbedding.Paper.IncrementsOriginalNativeCoordinates
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Original linear tensor functional coordinate views

Source: main.tex594–611 and the original input profile. Reuse the formally
accepted native-data/coordinate provider21d21. Only actual SYMMETRIC covariant
coordinate tensors are passed to the original L fields. No skew-extension
control, alternate norm/carrier or supplied coefficient estimate is introduced.
-/

noncomputable section
open Manifold
open scoped ContDiff ENNReal

namespace GlobalEmbedding.Paper

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]

/-- The actual forward source-chart differential in literal coordinate values.
It is the covariant counterpart of the existing inverse-chart tangent vectors;
no basis, metric or norm is supplied as replacement geometric data.
Source: original coordinate representation of the linear tensor functionals. -/
def incrementsOriginalSourceChartDifferential (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count) (x : M) :
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap.comp
    ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (D.atlas.chart i x)).toContinuousLinearMap.comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          (D.atlas.chart i) x))

/-- A genuine symmetric covariant coordinate tensor at the SAME native point.
Native Matrix.toBilin' and symmetric(Ers+Esr)/2 are pulled through the actual
chart differential. The certificate prevents any arbitrary skew extension of
the original linear functional from entering its coordinate profile.
Source: original linear ell_nu on the symmetric tensor fiber, main.tex594–599. -/
def incrementsOriginalSymmetricCoordinateTensor (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count) (x : M) (r s : Fin n) :
    {B : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) //
      B.IsSymm} := by
  let A := incrementsOriginalSourceChartDifferential D i x
  let C : Matrix (Fin n) (Fin n) ℝ := (1 / 2 : ℝ) •
    (Matrix.single r s 1 + (Matrix.single r s 1).transpose)
  have hC : C.IsSymm := (Matrix.isSymm_add_transpose_self _).smul (1 / 2 : ℝ)
  refine ⟨LinearMap.BilinForm.comp C.toBilin' A.toLinearMap A.toLinearMap, ?_⟩
  exact ⟨fun v w ↦ (Matrix.isSymm_toBilin'_iff_isSymm.mpr hC).eq (A v) (A w)⟩

/-- Actual linear-functional coefficients on ALL ordered symmetric coordinate
tensors. The values are DERIVED from the SAME native L field and chart, never
supplied coefficient data. Source: original finite weighted input profile. -/
def incrementsOriginalLinearArgumentCoordinates (D : IncrementsOriginalNativeData n d N M P)
    (ν : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount)
    (y : Fin (n + d) → ℝ) : Fin (n * n) → ℝ :=
  fun k ↦ D.linearArgument ν (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1
    (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2
    (incrementsOriginalSymmetricCoordinateTensor D i.1
      (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).val

/-- The actual original CORE profile including its genuine linear-functional
coordinate fields. It is STILL NOT the complete original profile: actual
adapted transition/inverse coordinate fields remain explicit missing edges.
No inverse/mean/solver output or skew-extension bound is an input.
Source: original linear ell_nu data and the W1 original finite input list. -/
def incrementsOriginalInputProfileWithLinear (D : IncrementsOriginalNativeData n d N M P)
    (j : ℕ) (ell : ℝ) : ℝ≥0∞ :=
  max (incrementsOriginalCoreInputProfile D j ell)
    (⨆ ν : Fin D.primaryCount,
      paperAtlasWeighted 0 j ell (incrementsOriginalLinearArgumentCoordinates D ν)
        (incrementsOriginalPrimaryDifferentiation D ν) (incrementsOriginalPrimaryEvaluation D ν))

end GlobalEmbedding.Paper
