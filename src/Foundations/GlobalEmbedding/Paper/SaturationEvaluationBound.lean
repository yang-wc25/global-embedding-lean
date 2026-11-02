import GlobalEmbedding.Paper.SaturationOriginalCone
import GlobalEmbedding.Paper.SaturationEuclideanModel
import GlobalEmbedding.Paper.SaturationEuclideanContraction
import GlobalEmbedding.Paper.ContractionCovectorFamily
import GlobalEmbedding.Paper.QuadraticSpaceDimension

/-!
# The SAME original intersection has a global Euclidean evaluation bound

Source: original `prop:saturation`, lines971–995. W1 supplies the actual faithful
Euclidean model of the SAME quotient over the original norm-only source V. The
maximum-rank open frame meets the actual good locus. The bound is therefore global
before applying W1's accepted dimension theorem. Actual W1/W2 dictionary providers
are instantiated internally; no dictionary or rank condition is an extra hypothesis.
-/

noncomputable section
open scoped Topology

namespace GlobalEmbedding.Paper

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The SAME actual mapped intersection has evaluation rank at most dim ker B at
ALL Euclidean points. A good maximal point is derived from actual Gram density.
Source: original `prop:saturation`, the global evaluation-rank step. -/
theorem saturation_operator_global_evaluation_bound
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B) :
    let P := (saturationContractionIntersection B).map (saturationEuclideanOperator V)
    ∀ x : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      Module.finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤
        Module.finrank ℝ B.ker := by
  let f := saturationEuclideanOperator V
  let P := (saturationContractionIntersection B).map f
  change ∀ x, Module.finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤ _
  obtain ⟨x₀, hmax⟩ := quadraticSpace_exists_maximal_evaluation P
  obtain ⟨A, _, hlocal⟩ := quadraticSpace_maximal_evaluation_frame P x₀ hmax
  obtain ⟨U, hsub, hopen, hx₀⟩ := mem_nhds_iff.mp hlocal
  let g := saturationEuclideanCovectors V
  let e := saturationEuclideanCoordinates V
  let T : (V →L[ℝ] ℝ) →ₗ[ℝ] (SymmetricSquare V →ₗ[ℝ] V) :=
    contractionKernelCovectorLinear.comp (ContinuousLinearMap.coeLM ℝ)
  obtain ⟨ξ, ⟨x, hx, rfl⟩, hgood⟩ := saturation_good_meets_open_of_linear_family
    B hB T (fun _ ↦ rfl) (g '' U) (g.isOpenMap U hopen) ⟨g x₀, x₀, hx₀, rfl⟩
  have hle : LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap ≤
      (B.ker.map (contractionKernelQuotientMap (g x).toLinearMap)).map e.toLinearMap := by
    rintro _ ⟨Q, rfl⟩
    obtain ⟨q, hq, heq⟩ := Submodule.mem_map.mp Q.property
    change (Q : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) x ∈ _
    rw [← heq, saturationEuclideanOperator_contraction]
    exact Submodule.mem_map.mpr ⟨_, (Submodule.mem_iInf _).mp hq ⟨g x, hgood⟩, rfl⟩
  have hrank :
      Module.finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap) =
        Module.finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) := by
    rw [← (hsub hx).2, LinearMap.finrank_range_of_inj (hsub hx).1]
  have hbound := (Submodule.finrank_mono hle).trans
    ((Submodule.finrank_map_le e.toLinearMap
      (B.ker.map (contractionKernelQuotientMap (g x).toLinearMap))).trans
      (Submodule.finrank_map_le (contractionKernelQuotientMap (g x).toLinearMap) B.ker))
  intro y
  exact (hmax y).trans (hrank.trans_le hbound)

/-- The exact original intersection satisfies the sharp dimension bound, using W1's
actual Euclidean model and its full dimension theorem. No source inner product,
good maximal point, global rank bound or classification conclusion is assumed.
Source: original `prop:saturation`, equation(9.1). -/
theorem saturation_contractionIntersection_dimension_bound
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B) :
    Module.finrank ℝ (saturationContractionIntersection B) ≤
      Module.finrank ℝ B.ker * (Module.finrank ℝ B.ker + 1) / 2 := by
  let R := saturationContractionIntersection B
  let P := R.map (saturationEuclideanOperator V)
  have hb := quadraticSpace_dimension_bound P (saturationEuclideanOperator_symmetric V R)
    (Module.finrank ℝ B.ker) (saturation_operator_global_evaluation_bound B hB)
  rw [← saturationEuclideanOperator_finrank V R] at hb
  exact hb

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.saturation_operator_global_evaluation_bound
#print axioms GlobalEmbedding.Paper.saturation_contractionIntersection_dimension_bound
