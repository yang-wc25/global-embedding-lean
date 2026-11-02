import GlobalEmbedding.Paper.SaturationOriginalData
import GlobalEmbedding.Paper.ContractionKernelDictionary
import GlobalEmbedding.Paper.SaturationOrthogonalIdentity
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The actual contraction intersection and original legal value span

Source: original `prop:saturation`, lines979–985. The sole canonical contraction
kernel identity identifies two honest intermediate submodules. The original
existential-cone carrier is not redefined or assumed equal to this intersection.
-/

namespace GlobalEmbedding.Paper

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual contraction-image preimage equals the actual restricted-B preimage.
Source: the kernel subtraction argument in original `prop:saturation`. -/
theorem saturation_contraction_preimage_eq
    [AddCommGroup W] [Module ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W) (ξ : V →ₗ[ℝ] ℝ) (hξ : ξ ≠ 0) :
    (B.ker.map (contractionKernelQuotientMap ξ)).comap
        (contractionKernelQuotientMap ξ) =
      (((symmetricSquareLinearMap ξ.ker.subtype).range).map B).comap B := by
  rw [Submodule.comap_map_eq, Submodule.comap_map_eq,
    contractionKernel_ker_eq_range ξ hξ, sup_comm]

/-- The SAME good-covector intersection is a common restricted-image preimage.
This is an intermediate identity, not a change of the original cone definition.
Source: original `prop:saturation`, the full family of good covectors. -/
theorem saturation_contractionIntersection_eq_commonPreimage
    [AddCommGroup W] [Module ℝ W] (B : SymmetricSquare V →ₗ[ℝ] W) :
    saturationContractionIntersection B =
      ⨅ ξ : {ξ : V →L[ℝ] ℝ // LinearSecondFormGoodCovector B ξ.toLinearMap},
        (((symmetricSquareLinearMap ξ.val.toLinearMap.ker.subtype).range).map B).comap B := by
  apply iInf_congr
  intro ξ
  exact saturation_contraction_preimage_eq B ξ.val.toLinearMap ξ.property.1

/-- The actual legal value span has the image of the actual contraction intersection
as its orthogonal complement. Phase regularity supplies the nonempty index internally.
Source: original `prop:saturation`, equation(9.1) after the cone identification. -/
theorem saturation_legalValueSpan_orthogonal
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B) :
    (saturationLegalValueSpan B).orthogonal = (saturationContractionIntersection B).map B := by
  have := saturation_good_continuous_covector_nonempty B hB
  rw [saturation_contractionIntersection_eq_commonPreimage]
  simpa only [saturationLegalValueSpan, supportedRankLegalValueSpace,
    LinearMap.range_comp] using saturation_orthogonal_common_preimage B
    (fun ξ : {ξ : V →L[ℝ] ℝ // LinearSecondFormGoodCovector B ξ.toLinearMap} ↦
      (symmetricSquareLinearMap ξ.val.toLinearMap.ker.subtype).range)

/-- Exact actual value dimension, with no target-surjectivity assumption.
Source: original `prop:saturation`, equation(9.3) after the cone identification. -/
theorem saturation_legalValueSpan_dimension
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B) :
    Module.finrank ℝ (saturationLegalValueSpan B) = Module.finrank ℝ W -
      (Module.finrank ℝ (saturationContractionIntersection B) - Module.finrank ℝ B.ker) := by
  have hm := saturation_image_dimension B (saturationContractionIntersection B)
    (saturation_kernel_le_contractionIntersection B)
  have ho := Submodule.finrank_add_finrank_orthogonal (saturationLegalValueSpan B)
  rw [saturation_legalValueSpan_orthogonal B hB] at ho
  omega

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.saturation_contraction_preimage_eq
#print axioms GlobalEmbedding.Paper.saturation_contractionIntersection_eq_commonPreimage
#print axioms GlobalEmbedding.Paper.saturation_legalValueSpan_orthogonal
#print axioms GlobalEmbedding.Paper.saturation_legalValueSpan_dimension
