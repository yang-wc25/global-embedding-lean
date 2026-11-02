import GlobalEmbedding.Paper.SaturationOriginalCone
import GlobalEmbedding.Paper.SaturationContractionValues
import GlobalEmbedding.Paper.ContractionCovectorFamily
import GlobalEmbedding.Paper.LinearSecondFormGoodOpen

/-!
# The literal ORIGINAL saturation subspace

Source: original `prop:saturation`, lines947–985. All dictionary parameters are
discharged by the actual canonical contraction and Good providers. The submodule
has literally the original existential-open-cone carrier. Its original phase
hypothesis is a proof-only parameter; there is no fallback carrier outside it.
-/

noncomputable section

namespace GlobalEmbedding.Paper

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

section Algebraic
variable [AddCommGroup W] [Module ℝ W]

/-- Actual cone equality, with ALL generic dictionary inputs eliminated.
Source: original `prop:saturation`, polynomial continuation of the original cone. -/
theorem saturation_originalSet_eq_intersection
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B) :
    originalSaturationSet B = (saturationContractionIntersection B : Set (SymmetricSquare V)) := by
  apply saturation_originalSet_eq_intersection_of_linear_family B hB
    (contractionKernelCovectorLinear.comp (ContinuousLinearMap.coeLM ℝ)) (fun _ ↦ rfl)
    (isOpen_linearSecondFormGoodCovector B)
  intro t ht ξ hξ
  exact (linearSecondFormGoodCovector_continuous_smul_iff B ξ t (ne_of_gt ht)).mpr hξ

/-- The ORIGINAL saturation submodule with its literal existential cone carrier.
The original phase proof is needed because the raw set can be empty otherwise.
Source: original `prop:saturation`, definition of R(K). -/
def originalSaturationSpace
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B) :
    Submodule ℝ (SymmetricSquare V) :=
  (saturationContractionIntersection B).copy (originalSaturationSet B)
    (saturation_originalSet_eq_intersection B hB)

/-- Carrier membership is literally ORIGINAL cone membership, not a universal shortcut.
Source: the original definition of R(K) in `prop:saturation`. -/
theorem mem_originalSaturationSpace_iff
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B)
    (P : SymmetricSquare V) :
    P ∈ originalSaturationSpace B hB ↔ P ∈ originalSaturationSet B := Iff.rfl

/-- The original cone submodule equals the proved intermediate intersection.
This equality is used in proofs; it does not replace the original data definition.
Source: original `prop:saturation`, the all-good consequence. -/
theorem originalSaturationSpace_eq_intersection
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B) :
    originalSaturationSpace B hB = saturationContractionIntersection B := by
  apply SetLike.coe_injective
  exact saturation_originalSet_eq_intersection B hB

/-- The SAME actual kernel belongs to the ORIGINAL saturation submodule.
Source: original `prop:saturation`, K is contained in R(K). -/
theorem saturation_kernel_le_originalSpace
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B) :
    B.ker ≤ originalSaturationSpace B hB := by
  rw [originalSaturationSpace_eq_intersection]
  exact saturation_kernel_le_contractionIntersection B

/-- Actual Good covectors meet every full-dual nonempty open set. No linear family,
Gram determinant, density, or inner product is assumed as an extra final premise.
Source: original `prop:saturation`, the global evaluation-rank argument. -/
theorem saturation_good_meets_open
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B)
    (U : Set (V →L[ℝ] ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ξ ∈ U, LinearSecondFormGoodCovector B ξ.toLinearMap :=
  saturation_good_meets_open_of_linear_family B hB
    (contractionKernelCovectorLinear.comp (ContinuousLinearMap.coeLM ℝ))
    (fun _ ↦ rfl) U hU hne

/-- At every ACTUAL good covector, SAME-R contraction image is exactly SAME-K image.
Source: original `prop:saturation`, evaluation rank is exactly d on the good locus. -/
theorem originalSaturationSpace_good_image_eq
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B)
    (ξ : V →L[ℝ] ℝ) (hξ : LinearSecondFormGoodCovector B ξ.toLinearMap) :
    (originalSaturationSpace B hB).map (contractionKernelQuotientMap ξ.toLinearMap) =
      B.ker.map (contractionKernelQuotientMap ξ.toLinearMap) := by
  apply le_antisymm
  · rintro _ ⟨q, hq, rfl⟩
    rw [originalSaturationSpace_eq_intersection] at hq
    exact (Submodule.mem_iInf _).mp hq ⟨ξ, hξ⟩
  · exact Submodule.map_mono (saturation_kernel_le_originalSpace B hB)

/-- The ACTUAL good evaluation image has exactly the original kernel dimension.
This is a proved local rank identity, distinct from the separately proved ALL-point bound.
Source: original `prop:saturation`, attaining d for the equality classification. -/
theorem originalSaturationSpace_good_image_finrank
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B)
    (ξ : V →L[ℝ] ℝ) (hξ : LinearSecondFormGoodCovector B ξ.toLinearMap) :
    Module.finrank ℝ
      ((originalSaturationSpace B hB).map (contractionKernelQuotientMap ξ.toLinearMap)) =
        Module.finrank ℝ B.ker := by
  rw [originalSaturationSpace_good_image_eq B hB ξ hξ]
  have hi := ((linearSecondFormGoodCovector_iff_contraction B ξ.toLinearMap).mp hξ).2
  have h := LinearMap.finrank_range_of_inj
    (f := (contractionKernelQuotientMap ξ.toLinearMap).domRestrict B.ker) hi
  rw [LinearMap.range_domRestrict] at h
  exact h

end Algebraic

section LegalValue
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- Full original orthogonal identity for the SAME actual R(K) and legal span.
Source: original `prop:saturation`, equation(9.1). -/
theorem originalSaturationSpace_legalValueSpan_orthogonal
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B) :
    (saturationLegalValueSpan B).orthogonal = (originalSaturationSpace B hB).map B := by
  rw [originalSaturationSpace_eq_intersection]
  exact saturation_legalValueSpan_orthogonal B hB

/-- Exact original legal-value dimension formula, without B surjectivity.
Source: original `prop:saturation`, equation(9.3). -/
theorem originalSaturationSpace_legalValueSpan_dimension
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B) :
    Module.finrank ℝ (saturationLegalValueSpan B) = Module.finrank ℝ W -
      (Module.finrank ℝ (originalSaturationSpace B hB) - Module.finrank ℝ B.ker) := by
  rw [originalSaturationSpace_eq_intersection]
  exact saturation_legalValueSpan_dimension B hB

end LegalValue
end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.saturation_originalSet_eq_intersection
#print axioms GlobalEmbedding.Paper.originalSaturationSpace
#print axioms GlobalEmbedding.Paper.mem_originalSaturationSpace_iff
#print axioms GlobalEmbedding.Paper.originalSaturationSpace_eq_intersection
#print axioms GlobalEmbedding.Paper.saturation_kernel_le_originalSpace
#print axioms GlobalEmbedding.Paper.saturation_good_meets_open
#print axioms GlobalEmbedding.Paper.originalSaturationSpace_good_image_eq
#print axioms GlobalEmbedding.Paper.originalSaturationSpace_good_image_finrank
#print axioms GlobalEmbedding.Paper.originalSaturationSpace_legalValueSpan_orthogonal
#print axioms GlobalEmbedding.Paper.originalSaturationSpace_legalValueSpan_dimension
