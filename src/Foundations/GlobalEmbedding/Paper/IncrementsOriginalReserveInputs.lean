import GlobalEmbedding.Paper.IncrementsOriginalQualitativeAdmissibility
import GlobalEmbedding.Paper.IncrementsOriginalLinearArgumentCoordinates

/-!
# Original given positive reserve and smooth linear coefficient inputs

Source: main.tex594–601,659–675. The reserve belongs to the ORIGINAL given
positive decomposition on its ORIGINAL neighborhood. No computed iterate,
mean, inverse, or desired output estimate is assumed. Required supports are
actual relative JOINT cutoff supports over the stated compact parameter set;
no arbitrary outside extension or slice-only support is substituted.
DAG: increments-original-reserve-linear-smooth-input. Exclusive worker W3.
-/

noncomputable section
open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]

/-- The ORIGINAL given uniform square-root reserve. This constrains only the
original decomposition neighborhood and original required joint supports over K.
It does not assert that any computed A_l satisfies the reserve or lies in that
neighborhood; those finite-domain checks remain outputs. The constant belongs
to the original structural data before quantitative uniformity quantifiers.
Source: positive reserve in594–601 and actual domain checks659–662. -/
structure IncrementsOriginalDecompositionReserveInputs
    (D : IncrementsOriginalNativeData n d N M P) (rho : ℝ) : Prop where
  reserve_pos : 0 < rho
  lower : ∀ ν z, z ∈ incrementsOriginalRelativeCutoffSupport D ν →
    z.1 ∈ D.parameterSet → ∀ A ∈ D.tensorNeighborhood z.1 z.2,
      rho ≤ D.linearArgument ν z.1 z.2 A.val

/-- Actual ORIGINAL smoothness of the given linear tensor-functional coefficient
fields, tested only on the genuine symmetric coordinate tensors. All source
and parameter variables are differentiated; no arbitrary skew extension is
controlled. Finite weighted bounds alone cannot replace smoothness because
native fderiv is totalized. Source: fixed smooth decomposition/finite parameter
input594–601 and product/chain-rule smoothness clause672–675. -/
structure IncrementsOriginalLinearSmoothInputs
    (D : IncrementsOriginalNativeData n d N M P) : Prop where
  linear_coordinates : ∀ ν i, ContDiffOn ℝ ∞
    (incrementsOriginalLinearArgumentCoordinates D ν i)
    (incrementsOriginalPrimaryDifferentiation D ν i ∩
      (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
        incrementsOriginalParameterRegion D)

end GlobalEmbedding.Paper
