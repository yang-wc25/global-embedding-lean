import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Common image preimages, orthogonal value span and actual dimensions

Source: `literature/parallelizable-stable-plus-one/main.tex`, prop:saturation proof.
This is the genuine linear bridge after identifying the ORIGINAL open-cone saturation
with the common preimage. It does not define the original set by a desired image identity.
No surjectivity of B is assumed: one genuine index supplies the needed preimage.
-/

namespace GlobalEmbedding.Paper

/-- A nonempty family of actual restricted images has a common preimage precisely
when its elements lie in their intersection. Native map/comap identities apply because
that intersection lies in range B, using one index rather than B surjectivity.
Source: prop:saturation, choosing a preimage from one good covector. -/
theorem saturation_common_preimage_map
    {E W ι : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup W] [Module ℝ W]
    [Nonempty ι] (B : E →ₗ[ℝ] W) (H : ι → Submodule ℝ E) :
    (⨅ i, ((H i).map B).comap B).map B = ⨅ i, (H i).map B := by
  rw [← Submodule.comap_iInf]
  apply Submodule.map_comap_eq_self
  exact (iInf_le _ (Classical.arbitrary ι)).trans LinearMap.map_le_range

/-- The actual kernel lies in every common image preimage, with no dimension or
nonempty-index requirement. Source: prop:saturation, K is contained in R(K). -/
theorem saturation_kernel_le_common_preimage
    {E W ι : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup W] [Module ℝ W]
    (B : E →ₗ[ℝ] W) (H : ι → Submodule ℝ E) :
    LinearMap.ker B ≤ ⨅ i, ((H i).map B).comap B := by
  apply le_iInf
  intro i x hx
  change B x ∈ (H i).map B
  rw [LinearMap.mem_ker.mp hx]
  exact Submodule.zero_mem _

/-- The complement of the span of the actual legal normal spaces is the actual
image of the common preimage. No chosen finite list or target-surjectivity assumption.
Source: prop:saturation, the full orthogonal/value-space identity. -/
theorem saturation_orthogonal_common_preimage
    {E W ι : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [Nonempty ι] (B : E →ₗ[ℝ] W) (H : ι → Submodule ℝ E) :
    (⨆ i, ((H i).map B).orthogonal).orthogonal =
      (⨅ i, ((H i).map B).comap B).map B := by
  rw [← Submodule.iInf_orthogonal]
  simp only [Submodule.orthogonal_orthogonal]
  exact (saturation_common_preimage_map B H).symm

/-- Restricting the actual map to a subspace containing its kernel preserves exactly
that kernel's dimension. Native rank-nullity supplies the image dimension identity.
Source: prop:saturation, dim B(R)=dim R-d, including d=0. -/
theorem saturation_image_dimension
    {E W : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup W] [Module ℝ W]
    (B : E →ₗ[ℝ] W) (R : Submodule ℝ E) (hK : LinearMap.ker B ≤ R) :
    Module.finrank ℝ (R.map B) + Module.finrank ℝ (LinearMap.ker B) =
      Module.finrank ℝ R := by
  have h := LinearMap.finrank_range_add_finrank_ker (B.domRestrict R)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [(Submodule.comapSubtypeEquivOfLe hK).finrank_eq] at h
  exact h

/-- The actual legal value dimension is the target dimension minus the common
preimage dimension less the original kernel dimension. Natural subtraction is
justified by actual rank-nullity, not an assumed numerical bound or surjectivity.
Source: prop:saturation, equation(9.3). -/
theorem saturation_common_preimage_value_dimension
    {E W ι : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [Nonempty ι] (B : E →ₗ[ℝ] W) (H : ι → Submodule ℝ E) :
    Module.finrank ℝ ((⨆ i, ((H i).map B).orthogonal) : Submodule ℝ W) =
      Module.finrank ℝ W -
        (Module.finrank ℝ ((⨅ i, ((H i).map B).comap B) : Submodule ℝ E) -
          Module.finrank ℝ (LinearMap.ker B)) := by
  have hm := saturation_image_dimension B (⨅ i, ((H i).map B).comap B)
    (saturation_kernel_le_common_preimage B H)
  have ho := Submodule.finrank_add_finrank_orthogonal (⨆ i, ((H i).map B).orthogonal)
  rw [saturation_orthogonal_common_preimage B H] at ho
  omega

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.saturation_common_preimage_map
#print axioms GlobalEmbedding.Paper.saturation_kernel_le_common_preimage
#print axioms GlobalEmbedding.Paper.saturation_orthogonal_common_preimage
#print axioms GlobalEmbedding.Paper.saturation_image_dimension
#print axioms GlobalEmbedding.Paper.saturation_common_preimage_value_dimension
