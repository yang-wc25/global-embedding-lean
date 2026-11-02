import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# The actual good hyperplane under a change of coframe

Source: `prop:initialization`, final paragraph.  If `c` is the actual uniformly
invertible coefficient map in a rescaled chart and `ξ` is the selector's good
covector, its pullback has a canonical kernel equivalence.  Normalizing the
pullback changes neither this hyperplane nor its induced norm.  The inverse
bound below is proved from the *same* coefficient inverse, not supplied as an
additional phase-stability hypothesis.
-/

noncomputable section

namespace GlobalEmbedding.Initialization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restrict the actual coefficient equivalence to the actual pulled-back
hyperplane.  No chosen basis of either kernel occurs. -/
def coefficientKernelEquiv (c : E ≃L[ℝ] F) (ξ : F →L[ℝ] ℝ) :
    (ξ.comp c.toContinuousLinearMap).ker ≃L[ℝ] ξ.ker :=
  c.ofSubmodule' ξ.ker

@[simp] theorem coefficientKernelEquiv_apply (c : E ≃L[ℝ] F)
    (ξ : F →L[ℝ] ℝ) (v : (ξ.comp c.toContinuousLinearMap).ker) :
    (coefficientKernelEquiv c ξ v : F) = c (v : E) := rfl

@[simp] theorem coefficientKernelEquiv_symm_apply (c : E ≃L[ℝ] F)
    (ξ : F →L[ℝ] ℝ) (v : ξ.ker) :
    ((coefficientKernelEquiv c ξ).symm v : E) = c.symm (v : F) := rfl

/-- Restriction to the actual hyperplanes cannot increase the inverse norm. -/
theorem coefficientKernelEquiv_inverse_norm_le (c : E ≃L[ℝ] F)
    (ξ : F →L[ℝ] ℝ) :
    ‖(coefficientKernelEquiv c ξ).symm.toContinuousLinearMap‖ ≤
      ‖c.symm.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact c.symm.toContinuousLinearMap.le_opNorm (v : F)

/-- A genuine nonzero selector covector stays nonzero under the actual coframe
equivalence.  This is needed before normalizing it. -/
theorem coefficientCovector_ne_zero (c : E ≃L[ℝ] F)
    (ξ : F →L[ℝ] ℝ) (hξ : ξ ≠ 0) :
    ξ.comp c.toContinuousLinearMap ≠ 0 := by
  intro h
  apply hξ
  ext v
  have hv := congrArg (fun L : E →L[ℝ] ℝ ↦ L (c.symm v)) h
  simpa using hv

/-- The unit covector defining the very same pulled-back hyperplane. -/
def unitCoefficientCovector (c : E ≃L[ℝ] F) (ξ : F →L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  NormedSpace.normalize (ξ.comp c.toContinuousLinearMap)

theorem unitCoefficientCovector_norm (c : E ≃L[ℝ] F)
    (ξ : F →L[ℝ] ℝ) (hξ : ξ ≠ 0) : ‖unitCoefficientCovector c ξ‖ = 1 := by
  exact NormedSpace.norm_normalize (coefficientCovector_ne_zero c ξ hξ)

theorem unitCoefficientCovector_ker (c : E ≃L[ℝ] F)
    (ξ : F →L[ℝ] ℝ) (hξ : ξ ≠ 0) :
    (unitCoefficientCovector c ξ).ker = (ξ.comp c.toContinuousLinearMap).ker := by
  ext v
  have hn : ‖ξ.comp c.toContinuousLinearMap‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (coefficientCovector_ne_zero c ξ hξ)
  simp [unitCoefficientCovector, NormedSpace.normalize,
    LinearMap.mem_ker, hn]

/-- The normalized kernel equivalence has the same concrete forward map `c`.
The equality transport here is just subtype identity, hence costs no norm factor. -/
def unitCoefficientKernelEquiv (c : E ≃L[ℝ] F)
    (ξ : F →L[ℝ] ℝ) (hξ : ξ ≠ 0) :
    (unitCoefficientCovector c ξ).ker ≃L[ℝ] ξ.ker :=
  (ContinuousLinearEquiv.ofEq _ _ (unitCoefficientCovector_ker c ξ hξ)).trans
    (coefficientKernelEquiv c ξ)

@[simp] theorem unitCoefficientKernelEquiv_apply (c : E ≃L[ℝ] F)
    (ξ : F →L[ℝ] ℝ) (hξ : ξ ≠ 0)
    (v : (unitCoefficientCovector c ξ).ker) :
    (unitCoefficientKernelEquiv c ξ hξ v : F) = c (v : E) := rfl

@[simp] theorem unitCoefficientKernelEquiv_symm_apply (c : E ≃L[ℝ] F)
    (ξ : F →L[ℝ] ℝ) (hξ : ξ ≠ 0) (v : ξ.ker) :
    ((unitCoefficientKernelEquiv c ξ hξ).symm v : E) = c.symm (v : F) := rfl

/-- The inverse kernel bound required by the existing phase-stability theorem
is a consequence of the actual coefficient inverse bound. -/
theorem unitCoefficientKernelEquiv_inverse_norm_le (c : E ≃L[ℝ] F)
    (ξ : F →L[ℝ] ℝ) (hξ : ξ ≠ 0) :
    ‖(unitCoefficientKernelEquiv c ξ hξ).symm.toContinuousLinearMap‖ ≤
      ‖c.symm.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact c.symm.toContinuousLinearMap.le_opNorm (v : F)

end GlobalEmbedding.Initialization
