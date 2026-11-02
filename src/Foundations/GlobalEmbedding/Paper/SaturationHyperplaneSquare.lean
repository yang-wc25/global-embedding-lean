import GlobalEmbedding.Paper.ContractionKernelDictionary
import GlobalEmbedding.Paper.SymmetricSquareFinrank
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The actual symmetric-square image of an original hyperplane

Source: original `prop:saturation`, lines961–968 and990–995. Native linear algebra
identifies the original hyperplane as an actual nonzero covector kernel. The already
accepted kernel-inclusion injectivity and W4 dimension formula then give the actual
range dimension. No source norm or inner product, new quotient, or new basis is used.
-/

namespace GlobalEmbedding.Paper

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- A literal codimension-one subspace is an actual nonzero covector kernel.
Source: supporting hyperplanes in original `prop:saturation`. -/
theorem saturation_hyperplane_eq_kernel (U : Submodule ℝ V)
    (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V) :
    ∃ ξ : V →ₗ[ℝ] ℝ, ξ ≠ 0 ∧ U = ξ.ker := by
  have hlt : U < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro heq
    have hdim := congrArg (fun P : Submodule ℝ V ↦ Module.finrank ℝ P) heq
    simp only [finrank_top] at hdim
    omega
  obtain ⟨ξ, hξ, hle⟩ := U.exists_le_ker_of_lt_top hlt
  refine ⟨ξ, hξ, Submodule.eq_of_le_of_finrank_le hle ?_⟩
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hξ
  omega

/-- The actual original hyperplane inclusion has an injective symmetric square.
The proof directly reuses the canonical nonzero-covector kernel inclusion theorem.
Source: original `prop:saturation`, the actual subspace Sym²U. -/
theorem saturation_hyperplane_square_injective (U : Submodule ℝ V)
    (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V) :
    Function.Injective (symmetricSquareLinearMap U.subtype) := by
  obtain ⟨ξ, hξ, rfl⟩ := saturation_hyperplane_eq_kernel U hU
  exact contractionKernel_linearMap_injective ξ hξ

/-- Exact dimension of the actual Sym²U image in the SAME original quotient.
This invokes the accepted W4 formula, with injectivity proved rather than assumed.
Source: original `prop:saturation`, the supported equality dimension comparison. -/
theorem saturation_hyperplane_square_range_finrank (U : Submodule ℝ V)
    (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V) :
    Module.finrank ℝ (symmetricSquareLinearMap U.subtype).range =
      Module.finrank ℝ U * (Module.finrank ℝ U + 1) / 2 := by
  rw [LinearMap.finrank_range_of_inj (saturation_hyperplane_square_injective U hU),
    symmetricSquare_finrank]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.saturation_hyperplane_eq_kernel
#print axioms GlobalEmbedding.Paper.saturation_hyperplane_square_injective
#print axioms GlobalEmbedding.Paper.saturation_hyperplane_square_range_finrank
