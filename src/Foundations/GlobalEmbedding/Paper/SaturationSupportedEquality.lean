import GlobalEmbedding.Paper.SaturationOriginalSpace
import GlobalEmbedding.Paper.SaturationEvaluationBound
import GlobalEmbedding.Paper.SaturationEuclideanContraction
import GlobalEmbedding.Paper.QuadraticSpaceEquality
import GlobalEmbedding.Paper.SaturationHyperplaneSquare
import GlobalEmbedding.Paper.SupportedRankGoodContractionImage

/-!
# Actual equality classification of the ORIGINAL saturation space

Source: original `prop:saturation`, lines990–995. The original norm-only source,
literal cone carrier, actual quotient and every supporting subspace are preserved.
W1 supplies the full Euclidean equality theorem and the genuine coordinate model.
W5 proves the actual attained-rank clause and consumes the ALL-point rank bound.
The supported converse/uniqueness must consume the sole W6 good evaluation image
provider; no competing E/J map or supplied final saturation conclusion is introduced.
-/

noncomputable section

namespace GlobalEmbedding.Paper

section Algebraic
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Full sharp bound for the literal ORIGINAL cone submodule, without any dictionary,
coordinate, desired rank, convergence, or source-inner-product hypothesis.
Source: original `prop:saturation`, equation(9.1). -/
theorem originalSaturationSpace_dimension_bound
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B) :
    Module.finrank ℝ (originalSaturationSpace B hB) ≤
      Module.finrank ℝ B.ker * (Module.finrank ℝ B.ker + 1) / 2 := by
  rw [originalSaturationSpace_eq_intersection]
  exact saturation_contractionIntersection_dimension_bound B hB

/-- The SAME actual operator space attains kernel dimension at a genuine original
good covector. This is separate from, and compatible with, the ALL-point upper bound.
Source: original `prop:saturation`, exact maximal evaluation rank d. -/
theorem originalSaturationSpace_evaluation_attains
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B) :
    let P := (originalSaturationSpace B hB).map (saturationEuclideanOperator V)
    ∃ x : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      Module.finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) =
        Module.finrank ℝ B.ker := by
  obtain ⟨ξ, hξ⟩ := (saturation_phaseRegular_iff_continuous_covector B).mp hB
  refine ⟨(saturationEuclideanCovectors V).symm ξ, ?_⟩
  rw [saturationEuclideanOperator_evaluation_finrank,
    (saturationEuclideanCovectors V).apply_symm_apply ξ]
  exact originalSaturationSpace_good_image_finrank B hB ξ hξ

/-- Extremal dimension gives a genuine supporting d-plane in the ORIGINAL source,
and equality with its full original symmetric-square image. All coordinate/model/
classification premises are discharged by actual canonical providers.
Source: original `prop:saturation`, equality case; d>=2 is essential. -/
theorem originalSaturationSpace_support_of_dimension_eq
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B)
    (hd : 2 ≤ Module.finrank ℝ B.ker)
    (heq : Module.finrank ℝ (originalSaturationSpace B hB) =
      Module.finrank ℝ B.ker * (Module.finrank ℝ B.ker + 1) / 2) :
    ∃ U : Submodule ℝ V, Module.finrank ℝ U = Module.finrank ℝ B.ker ∧
      originalSaturationSpace B hB = (symmetricSquareLinearMap U.subtype).range := by
  let R := originalSaturationSpace B hB
  let P := R.map (saturationEuclideanOperator V)
  have hmax : ∀ x : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      Module.finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤
        Module.finrank ℝ B.ker := by
    have hP : P = (saturationContractionIntersection B).map
        (saturationEuclideanOperator V) :=
      congrArg (fun Q : Submodule ℝ (SymmetricSquare V) ↦
        Q.map (saturationEuclideanOperator V)) (originalSaturationSpace_eq_intersection B hB)
    have hp := congrArg (fun Q : Submodule ℝ
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ]
          EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ↦
      ∀ x, Module.finrank ℝ (LinearMap.range (quadraticSpaceEvaluation Q x).toLinearMap) ≤
        Module.finrank ℝ B.ker) hP
    exact Eq.mpr hp (saturation_operator_global_evaluation_bound B hB)
  have hdimP : Module.finrank ℝ P =
      Module.finrank ℝ B.ker * (Module.finrank ℝ B.ker + 1) / 2 :=
    (saturationEuclideanOperator_finrank V R).symm.trans heq
  obtain ⟨S, hS, hPS⟩ := quadraticSpace_equality_classification P
    (saturationEuclideanOperator_symmetric V R) (Module.finrank ℝ B.ker) hd hmax
    (originalSaturationSpace_evaluation_attains B hB) hdimP
  let e := saturationEuclideanCoordinates V
  let U := S.comap e.toLinearMap
  have hmap : U.map e.toLinearMap = S :=
    Submodule.map_comap_eq_of_surjective e.surjective S
  refine ⟨U, ?_, ?_⟩
  · have hdim := saturationEuclideanCoordinates_finrank V U
    rw [hmap] at hdim
    exact hdim.trans hS
  · exact (saturationEuclideanOperator_supported_iff V R S).mp hPS

/-- Every original supporting hyperplane gives equality with the FULL original R.
Actual supported good images come from the sole W6 provider; no E/J is rebuilt.
Source: original `prop:saturation`, the supported converse. -/
theorem originalSaturationSpace_eq_of_supported
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B)
    (U : Submodule ℝ V) (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V)
    (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U) :
    originalSaturationSpace B hB = (symmetricSquareLinearMap U.subtype).range := by
  have hle : (symmetricSquareLinearMap U.subtype).range ≤ originalSaturationSpace B hB := by
    intro q hq
    rw [originalSaturationSpace_eq_intersection]
    apply (Submodule.mem_iInf _).mpr
    intro ξ
    change contractionKernelQuotientMap ξ.val.toLinearMap q ∈
      B.ker.map (contractionKernelQuotientMap ξ.val.toLinearMap)
    rw [supportedRank_good_contraction_image B U hK ξ.val.toLinearMap ξ.property hdim]
    obtain ⟨r, rfl⟩ := hq
    rw [← contractionKernelQuotientMap_naturality_apply U.subtype ξ.val.toLinearMap r]
    exact (contractionKernelQuotientMap (ξ.val.toLinearMap.comp U.subtype) r).property
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [saturation_hyperplane_square_range_finrank U hU]
  have hr := originalSaturationSpace_dimension_bound B hB
  rw [hdim] at hr
  exact hr

/-- The SAME actual good image determines every supporting subspace of dimension d.
One original good covector suffices. This directly reuses W6 and adds no support
reflection theorem or choice of an extra good point as a final hypothesis.
Source: original `prop:saturation`, uniqueness of its supporting hyperplane. -/
theorem originalSaturationSpace_supported_unique
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B)
    (U U' : Submodule ℝ V)
    (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (hK' : B.ker ≤ (symmetricSquareLinearMap U'.subtype).range)
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U)
    (hdim' : Module.finrank ℝ B.ker = Module.finrank ℝ U') : U' = U := by
  obtain ⟨ξ, hξ⟩ := hB
  exact (supportedRank_good_contraction_image B U' hK' ξ hξ hdim').symm.trans
    (supportedRank_good_contraction_image B U hK ξ hξ hdim)

end Algebraic

section LegalValue
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- In the original onto dimension a supported kernel has exactly n ACTUAL legal
value directions. Rank-nullity and all kernel/range dimensions are genuine outputs.
Source: original `prop:saturation`, its supported value-span conclusion. -/
theorem originalSaturationSpace_supported_value_dimension
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B)
    (honto : Function.Surjective B)
    (hW : Module.finrank ℝ W =
      Module.finrank ℝ V * (Module.finrank ℝ V - 1) / 2 + 1)
    (U : Submodule ℝ V) (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V)
    (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range) :
    Module.finrank ℝ (saturationLegalValueSpan B) = Module.finrank ℝ V := by
  have hd := symmetricSquare_surjective_kernel_finrank B honto hW
  have hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U := by omega
  have hRU := originalSaturationSpace_eq_of_supported B hB U hU hK hdim
  have hv := originalSaturationSpace_legalValueSpan_dimension B hB
  have hk := Submodule.finrank_mono (saturation_kernel_le_originalSpace B hB)
  rw [hRU, saturation_hyperplane_square_range_finrank U hU] at hv hk
  rw [← hU, Nat.add_sub_cancel,
    Nat.mul_comm (Module.finrank ℝ U + 1) (Module.finrank ℝ U)] at hW
  omega

/-- In the original onto dimension, absence of a supported kernel gives at least
n+1 ACTUAL legal value directions. The extremal alternative is derived from exact
dimension arithmetic, then contradicted using the full actual classification.
Source: original `prop:saturation`, the nonsupported value-span conclusion. -/
theorem originalSaturationSpace_nonsupported_value_lower
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B)
    (honto : Function.Surjective B) (hn : 3 ≤ Module.finrank ℝ V)
    (hW : Module.finrank ℝ W =
      Module.finrank ℝ V * (Module.finrank ℝ V - 1) / 2 + 1)
    (hns : ¬ HasSupportedKernel B) :
    Module.finrank ℝ V + 1 ≤ Module.finrank ℝ (saturationLegalValueSpan B) := by
  have hd := symmetricSquare_surjective_kernel_finrank B honto hW
  have hn' : Module.finrank ℝ V = Module.finrank ℝ B.ker + 1 := by omega
  have hd₂ : 2 ≤ Module.finrank ℝ B.ker := by omega
  have hw' : Module.finrank ℝ W =
      Module.finrank ℝ B.ker * (Module.finrank ℝ B.ker + 1) / 2 + 1 := by
    rw [hn', Nat.add_sub_cancel,
      Nat.mul_comm (Module.finrank ℝ B.ker + 1) (Module.finrank ℝ B.ker)] at hW
    exact hW
  by_contra! hs
  have hr := originalSaturationSpace_dimension_bound B hB
  have hk := Submodule.finrank_mono (saturation_kernel_le_originalSpace B hB)
  have hv := originalSaturationSpace_legalValueSpan_dimension B hB
  have heq : Module.finrank ℝ (originalSaturationSpace B hB) =
      Module.finrank ℝ B.ker * (Module.finrank ℝ B.ker + 1) / 2 := by omega
  obtain ⟨U, hU, hRU⟩ := originalSaturationSpace_support_of_dimension_eq B hB hd₂ heq
  apply hns
  refine ⟨U, ?_, ?_⟩
  · omega
  · rw [← hRU]
    exact saturation_kernel_le_originalSpace B hB

end LegalValue
end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.originalSaturationSpace_dimension_bound
#print axioms GlobalEmbedding.Paper.originalSaturationSpace_evaluation_attains
#print axioms GlobalEmbedding.Paper.originalSaturationSpace_support_of_dimension_eq
#print axioms GlobalEmbedding.Paper.originalSaturationSpace_eq_of_supported
#print axioms GlobalEmbedding.Paper.originalSaturationSpace_supported_unique
#print axioms GlobalEmbedding.Paper.originalSaturationSpace_supported_value_dimension
#print axioms GlobalEmbedding.Paper.originalSaturationSpace_nonsupported_value_lower
