import Probes.ActualIncrementOriginalInputProfiles
import Smoothing.TensorEllipticity
import GlobalEmbedding.Paper.IncrementsOriginalDecompositionInputs

/-! The original C0 norm preserves the given positive linear arguments.
The input is the SAME native symmetric tensor. Chart indices are selected
from the actual source inner cover and actual parameter norm cover. There is
no hypothesis that a computed tensor still belongs to a prescribed fiber
neighborhood, and no bound on a mean or a solver output. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal BigOperators
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]

theorem parameterRound2_original_linear_argument_C0_bound
    (D : IncrementsOriginalNativeData n d N M P)
    (hAtlas : IsSmoothBufferedAtlas D.atlas)
    (input : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x))
    (ell ML R : ℝ)
    (hProfile : incrementsOriginalInputProfileWithLinear D 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear D 0 ell).toReal ≤ ML)
    (hFinite : paperAtlasCj 0 (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet) ≠ ⊤)
    (hR : (paperAtlasCj 0 (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet)).toReal ≤ R)
    (ν : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount)
    (y : Fin (n+d) → ℝ) (hy : y ∈ incrementsOriginalPrimaryEvaluation D ν i)
    (hSymm : (input (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1
      (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2).IsSymm) :
    |D.linearArgument ν (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1
      (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2
      (input (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1
        (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2)| ≤
      ‖actualOriginalCoefficientFunctional n‖ * ML * R := by
  let LC := incrementsOriginalLinearArgumentCoordinates D ν
  let AC := incrementsOriginalTensorCoordinates D.atlas D.parameterChart input
  have hLle : paperAtlasCj 0 LC (incrementsOriginalPrimaryDifferentiation D ν)
      (incrementsOriginalPrimaryEvaluation D ν) ≤ incrementsOriginalInputProfileWithLinear D 0 ell := by
    have h := (le_iSup (fun mu => paperAtlasWeighted 0 0 ell
      (incrementsOriginalLinearArgumentCoordinates D mu)
      (incrementsOriginalPrimaryDifferentiation D mu)
      (incrementsOriginalPrimaryEvaluation D mu)) ν).trans (le_max_right
        (incrementsOriginalCoreInputProfile D 0 ell) _)
    simpa only [LC, incrementsOriginalInputProfileWithLinear, paperAtlasWeighted,
      Finset.sum_range_one, pow_zero, zero_add, one_mul] using h
  have hL := (paperAtlasC0_value_le LC _ _ (ne_top_of_le_ne_top hProfile hLle) i hy).trans
    ((ENNReal.toReal_mono hProfile hLle).trans hML)
  have hA := (paperAtlasC0_value_le AC _ _ hFinite i hy.1).trans hR
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hA
  rw [actual_original_linear_argument_tensor_pairing D hAtlas input ν i y hy.1.1.1 hSymm]
  rw [← actualOriginalCoefficientFunctional_apply]
  change ‖actualOriginalCoefficientFunctional n (LC i y) (AC i y)‖ ≤ _
  calc
    _ ≤ ‖actualOriginalCoefficientFunctional n (LC i y)‖ * ‖AC i y‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖actualOriginalCoefficientFunctional n‖ * ‖LC i y‖) * ‖AC i y‖ :=
      mul_le_mul_of_nonneg_right ((actualOriginalCoefficientFunctional n).le_opNorm _) (norm_nonneg _)
    _ ≤ (‖actualOriginalCoefficientFunctional n‖ * ‖LC i y‖) * R :=
      mul_le_mul_of_nonneg_left hA
        (mul_nonneg (actualOriginalCoefficientFunctional n).opNorm_nonneg (norm_nonneg _))
    _ ≤ ‖actualOriginalCoefficientFunctional n‖ * ML * R :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL
        (actualOriginalCoefficientFunctional n).opNorm_nonneg) hR0

variable [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- Every actual point over K has a genuine original evaluation coordinate.
The selected chart can vary with the point, without entering any constant. -/
theorem parameterRound2_original_evaluation_cover
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (p : P) (hp : p ∈ D.parameterSet) (x : M) :
    ∃ (i : Fin D.atlas.count × Fin D.parameterCount) (y : Fin (n+d) → ℝ),
      y ∈ incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet i ∧
      incrementsOriginalJointPoint D.atlas D.parameterChart i y = (p,x) := by
  obtain ⟨a,ha⟩ := D.atlas.cover x
  obtain ⟨b,hb,hbn⟩ := hd.parameter_cover p hp
  let y := parameterTensorModelEquiv n d (D.parameterChart b p,D.atlas.chart a x)
  have hc : (incrementsOriginalParameterPoint y,incrementsOriginalSourcePoint y) =
      (D.parameterChart b p,D.atlas.chart a x) := by
    rw [← parameterTensorModelEquiv_symm_apply]
    exact (parameterTensorModelEquiv n d).symm_apply_apply _
  have hp' : incrementsOriginalParameterPoint y = D.parameterChart b p := congrArg Prod.fst hc
  have hx' : incrementsOriginalSourcePoint y = D.atlas.chart a x := congrArg Prod.snd hc
  have hpoint : incrementsOriginalJointPoint D.atlas D.parameterChart (a,b) y = (p,x) := by
    simp only [incrementsOriginalJointPoint, hp',hx',
      (D.parameterChart b).left_inv hb,(D.atlas.chart a).left_inv (D.atlas.inner_subset a ha)]
  refine ⟨(a,b),y,?_,hpoint⟩
  change (_ ∧ _) ∧ _ ∧ _ ∧ _
  rw [hp',hx',hpoint]
  exact ⟨⟨(D.atlas.chart a).map_source (D.atlas.inner_subset a ha),
    (D.parameterChart b).map_source hb⟩,hd.source_inner_norm a x ha,hbn,hp⟩

/-- C0 control of the SAME input minus H gives half of the original reserve
on every required joint support over K. Membership of the computed input in
the original tensorNeighborhood is a consequence no longer needed here. -/
theorem parameterRound2_original_reserve_of_C0
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs D)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs D rho)
    (input : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x))
    (hSymm : ∀ p ∈ D.parameterOpen, ∀ x, (input p x).IsSymm)
    (ell ML R : ℝ)
    (hProfile : incrementsOriginalInputProfileWithLinear D 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear D 0 ell).toReal ≤ ML)
    (hFinite : paperAtlasCj 0
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => input p x-D.H p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet) ≠ ⊤)
    (hR : (paperAtlasCj 0
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => input p x-D.H p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet)).toReal ≤ R)
    (hSmall : ‖actualOriginalCoefficientFunctional n‖ * ML * R ≤ rho/2) :
    ∀ ν z, z ∈ incrementsOriginalRelativeCutoffSupport D ν → z.1 ∈ D.parameterSet →
      rho/2 ≤ D.linearArgument ν z.1 z.2 (input z.1 z.2) := by
  intro ν z hz hp
  obtain ⟨i,y,hy,he⟩ := parameterRound2_original_evaluation_cover D hd z.1 hp z.2
  have hys : y ∈ incrementsOriginalPrimaryEvaluation D ν i :=
    ⟨hy,by change incrementsOriginalJointPoint D.atlas D.parameterChart i y ∈ D.primaryDomain ν
           simpa only [he, Prod.mk.eta] using hd.cutoff_support_local ν hz⟩
  have hsym : ((fun p x => input p x-D.H p x)
      (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1
      (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2).IsSymm := by
    rw [he]
    exact (hSymm z.1 (hd.parameter_subset hp) z.2).sub
      (hDecomp.H_symmetric z.1 (hd.parameter_subset hp) z.2)
  have h := parameterRound2_original_linear_argument_C0_bound D hd.atlas_smooth
    (fun p x => input p x-D.H p x) ell ML R hProfile hML hFinite hR ν i y hys hsym
  rw [he] at h
  change |D.linearArgument ν z.1 z.2 (input z.1 z.2-D.H z.1 z.2)| ≤ _ at h
  have hlin : D.linearArgument ν z.1 z.2 (input z.1 z.2-D.H z.1 z.2) =
      D.linearArgument ν z.1 z.2 (input z.1 z.2)-D.linearArgument ν z.1 z.2 (D.H z.1 z.2) :=
    map_sub (D.linearArgument ν z.1 z.2) _ _
  rw [hlin] at h
  have hH := hReserve.lower ν z hz hp _ (hDecomp.H_mem z.1 (hd.parameter_subset hp) z.2)
  change rho ≤ D.linearArgument ν z.1 z.2 (D.H z.1 z.2) at hH
  have hlo := (abs_le.mp h).1
  linarith

#print axioms parameterRound2_original_linear_argument_C0_bound
#print axioms parameterRound2_original_evaluation_cover
#print axioms parameterRound2_original_reserve_of_C0
end GlobalEmbedding.Continuation
