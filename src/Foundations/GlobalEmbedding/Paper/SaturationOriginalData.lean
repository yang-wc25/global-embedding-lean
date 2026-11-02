import GlobalEmbedding.Paper.SupportedLocusLocalEquations
import GlobalEmbedding.Paper.SupportedRankLegalVariation
import GlobalEmbedding.Paper.QuotientContraction
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The original open-cone saturation set and its literal value-space data

Source: `literature/parallelizable-stable-plus-one/main.tex`, prop:saturation947–968.
The raw existential cone set is kept literally. The universal contraction intersection
is explicitly an intermediate, not a new definition of the original saturation space.
Its equality with the original carrier must be proved before constructing that submodule.
Goodness, phase regularity and legal value spaces reuse their sole canonical definitions.
-/

noncomputable section

namespace GlobalEmbedding.Paper

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section Algebraic

variable [AddCommGroup W] [Module ℝ W]

/-- The ORIGINAL existential-open-cone carrier. The cone lives in full covector space,
is nonempty, and is invariant under positive scaling. No universal identity or desired
subspace closure is built into this definition. Source: prop:saturation, definition of R. -/
def originalSaturationSet (B : SymmetricSquare V →ₗ[ℝ] W) : Set (SymmetricSquare V) :=
  {P | ∃ C : Set (V →L[ℝ] ℝ), IsOpen C ∧ C.Nonempty ∧
    (∀ t : ℝ, 0 < t → ∀ ξ ∈ C, t • ξ ∈ C) ∧
    (∀ ξ ∈ C, LinearSecondFormGoodCovector B ξ.toLinearMap) ∧
    ∀ ξ ∈ C, contractionKernelQuotientMap ξ.toLinearMap P ∈
      B.ker.map (contractionKernelQuotientMap ξ.toLinearMap)}

/-- The actual universal contraction intersection, an honest INTERMEDIATE submodule.
Identifying its carrier with the original existential cone set is a separate theorem;
phase regularity is essential to that identification. Source: prop:saturation proof. -/
def saturationContractionIntersection (B : SymmetricSquare V →ₗ[ℝ] W) :
    Submodule ℝ (SymmetricSquare V) :=
  ⨅ ξ : {ξ : V →L[ℝ] ℝ // LinearSecondFormGoodCovector B ξ.toLinearMap},
    (B.ker.map (contractionKernelQuotientMap ξ.val.toLinearMap)).comap
      (contractionKernelQuotientMap ξ.val.toLinearMap)

/-- Continuous covectors cover exactly the original algebraic phase witness in finite
source dimension. This proves the conversion internally, without adding a witness
or a second good-covector predicate. Source: prop:saturation, phase regularity. -/
theorem saturation_phaseRegular_iff_continuous_covector [FiniteDimensional ℝ V]
    (B : SymmetricSquare V →ₗ[ℝ] W) :
    LinearSecondFormPhaseRegular B ↔
      ∃ ξ : V →L[ℝ] ℝ, LinearSecondFormGoodCovector B ξ.toLinearMap := by
  constructor
  · rintro ⟨ξ, hξ⟩
    exact ⟨ξ.toContinuousLinearMap, by simpa using hξ⟩
  · rintro ⟨ξ, hξ⟩
    exact ⟨ξ.toLinearMap, hξ⟩

/-- The actual good continuous-covector index type is nonempty under the ORIGINAL
phase hypothesis. No target surjectivity is used. Source: prop:saturation proof. -/
theorem saturation_good_continuous_covector_nonempty [FiniteDimensional ℝ V]
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B) :
    Nonempty {ξ : V →L[ℝ] ℝ // LinearSecondFormGoodCovector B ξ.toLinearMap} := by
  obtain ⟨ξ, hξ⟩ := (saturation_phaseRegular_iff_continuous_covector B).1 hB
  exact ⟨⟨ξ, hξ⟩⟩

/-- The actual B kernel belongs to the universal contraction intersection, directly
from its actual image under each contraction. This is not a cone-to-global theorem.
Source: prop:saturation proof, K is contained in the eventual saturation space. -/
theorem saturation_kernel_le_contractionIntersection
    (B : SymmetricSquare V →ₗ[ℝ] W) : B.ker ≤ saturationContractionIntersection B := by
  apply le_iInf
  intro ξ P hP
  exact Submodule.mem_map.mpr ⟨P, hP, rfl⟩

end Algebraic

section LegalValue

variable [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The original span of all legal normal value spaces, using the sole canonical
raw covector and literal restricted second-form image definitions. No finite wave
list or spanning conclusion is chosen. Source: prop:saturation, span over good ξ. -/
def saturationLegalValueSpan (B : SymmetricSquare V →ₗ[ℝ] W) : Submodule ℝ W :=
  ⨆ ξ : {ξ : V →L[ℝ] ℝ // LinearSecondFormGoodCovector B ξ.toLinearMap},
    supportedRankLegalValueSpace B ξ.val.toLinearMap

end LegalValue

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.originalSaturationSet
#print axioms GlobalEmbedding.Paper.saturationContractionIntersection
#print axioms GlobalEmbedding.Paper.saturation_phaseRegular_iff_continuous_covector
#print axioms GlobalEmbedding.Paper.saturation_good_continuous_covector_nonempty
#print axioms GlobalEmbedding.Paper.saturation_kernel_le_contractionIntersection
#print axioms GlobalEmbedding.Paper.saturationLegalValueSpan
