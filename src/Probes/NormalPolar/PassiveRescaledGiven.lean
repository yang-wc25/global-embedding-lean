import NormalPolar.PassiveRescaledData
import Probes.ActualOriginalGivenProfile
import Probes.ActualIncrementOriginalOpenCore
import Smoothing.ParameterRound2RepairNormAlgebra

/-! Reference contractions have cost at most one in the entire original
Given input norm. The actual norm, original differentiation domains and
samples remain fixed; only the F block is scalar-multiplied. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem passiveRescaledData_given_le (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hAll : Data.parameterSet = univ) (c : ℝ) (hc : |c| ≤ 1)
    (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hGiven : actualOriginalGivenInputProfile Data j ell ≠ ⊤) :
    actualOriginalGivenInputProfile (passiveRescaledData Data c) j ell ≤
      actualOriginalGivenInputProfile Data j ell := by
  let O := incrementsOriginalDifferentiation Data.atlas Data.parameterChart
  let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
    Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
  let f := incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F
  have hRegion : incrementsOriginalParameterRegion Data = (univ : Set (P × M)) := by
    apply Set.eq_univ_of_forall
    intro z
    exact ⟨hd.parameter_subset (by rw [hAll]; trivial),mem_univ _⟩
  have hf (i) : ContDiffOn ℝ ∞ (f i) (O i) := by
    have h := actual_original_map_coordinates_parameter_open Data hd hs i
    simpa only [hRegion,preimage_univ,inter_univ] using h
  have hMap : paperAtlasWeighted 2 j ell f O S ≤ actualOriginalGivenInputProfile Data j ell :=
    (show paperAtlasWeighted 2 j ell f O S ≤ incrementsOriginalCoreInputProfile Data j ell from
      le_max_left _ _).trans (actualOriginalGivenInputProfile_core_le Data j ell)
  have hFinite := ne_top_of_le_ne_top hGiven hMap
  have hTop := parameterRound2_topOrder_finite_of_weighted 2 j hell f O S hFinite
  have hSmul := parameterRound2_paperAtlasWeighted_smul_le 2 j ell f O S
    (parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart)
    (fun _ _ hy => hy.1) hf hTop c
  have hcE : ENNReal.ofReal |c| ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hc
  have hScale : paperAtlasWeighted 2 j ell (fun i y => c • f i y) O S ≤
      paperAtlasWeighted 2 j ell f O S :=
    hSmul.trans (by simpa only [mul_comm,mul_one,one_mul] using
      mul_le_mul_right hcE (paperAtlasWeighted 2 j ell f O S))
  unfold actualOriginalGivenInputProfile
  apply max_le_max ?_ le_rfl
  unfold incrementsOriginalInputProfileWithLinear
  apply max_le_max ?_ le_rfl
  unfold incrementsOriginalCoreInputProfile
  exact max_le_max hScale le_rfl

theorem passiveRescaledData_given_bound (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hAll : Data.parameterSet = univ) (c : ℝ) (hc : |c| ≤ 1)
    (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hGiven : actualOriginalGivenInputProfile Data j ell ≠ ⊤) :
    actualOriginalGivenInputProfile (passiveRescaledData Data c) j ell ≠ ⊤ ∧
    (actualOriginalGivenInputProfile (passiveRescaledData Data c) j ell).toReal ≤
      (actualOriginalGivenInputProfile Data j ell).toReal := by
  have h := passiveRescaledData_given_le Data hd hs hAll c hc j ell hell hGiven
  exact ⟨ne_top_of_le_ne_top hGiven h,ENNReal.toReal_mono hGiven h⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveRescaledData_given_le
#print axioms GlobalEmbedding.Continuation.passiveRescaledData_given_bound
