import GlobalEmbedding.Paper.ContractionCovectorFamily
import GlobalEmbedding.Paper.ContractionKernelDictionary
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The original supported good contraction image, without an inner product

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:saturation`,
lines 990–996, and `prop:supported-rank`, lines 1004–1012. This extracts the actual
image endpoint of the same good-evaluation argument without constructing another E/J.
-/

namespace GlobalEmbedding.Paper

/-- At an original good covector, the actual supported kernel contracts onto the SAME U.

Proof: write each actual supported kernel tensor using the original symmetric-square
inclusion. The sole canonical contraction naturality puts its image in the actual
subtype U. The original good/contraction dictionary proves injectivity on the SAME
ker B, so native range dimension equals `dim ker B=dim U`. Native finite-dimensional
submodule equality turns the inclusion into equality, including zero dimensions.
No norm, inner product, desired image premise or new evaluation structure is used.
Source: `prop:saturation`, supported converse and uniqueness, original `Kξ=U`. -/
theorem supportedRank_good_contraction_image
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W) (U : Submodule ℝ V)
    (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (ξ : V →ₗ[ℝ] ℝ) (hg : LinearSecondFormGoodCovector B ξ)
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U) :
    B.ker.map (contractionKernelQuotientMap ξ) = U := by
  have hle : B.ker.map (contractionKernelQuotientMap ξ) ≤ U := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨r, hr⟩ := hK hq
    rw [← hr, ← contractionKernelQuotientMap_naturality_apply U.subtype ξ r]
    exact (contractionKernelQuotientMap (ξ.comp U.subtype) r).property
  have hi := ((linearSecondFormGoodCovector_iff_contraction B ξ).mp hg).2
  have hd := LinearMap.finrank_range_of_inj
    (f := (contractionKernelQuotientMap ξ).domRestrict B.ker) hi
  rw [LinearMap.range_domRestrict] at hd
  exact Submodule.eq_of_le_of_finrank_le hle (by rw [hd, hdim])

#print axioms supportedRank_good_contraction_image

end GlobalEmbedding.Paper
