import Smoothing.ParameterRound2OriginalFiniteReserveGermSmooth

/-! The common finite positivity neighborhood is derived solely from the
original coordinate smoothness and original C0 data. Continuity of the
computed native linear arguments is proved internally at the actual compact
parameter samples. No assumption about a whole open set of computed tensors
or an output mean bound enters this construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

private theorem original_reserve_radius_bound (rho a : ℝ) (hrho : 0 < rho) (ha : 0 ≤ a) :
    0 < rho/(2*(a+1)) ∧ a*(rho/(2*(a+1))) ≤ rho/2 := by
  have had : 0 < a+1 := by linarith
  have hrad : 0 < rho/(2*(a+1)) := div_pos hrho (mul_pos (by norm_num) had)
  refine ⟨hrad,?_⟩
  calc
    a*(rho/(2*(a+1))) ≤ (a+1)*(rho/(2*(a+1))) :=
      mul_le_mul_of_nonneg_right (by linarith) hrad.le
    _ = rho/2 := by field_simp

/-- The actual original C0 seminorm reserve supplies one common positive,
smooth, exactly decomposing neighborhood for ANY finite list of real native
input germs. The radius is fixed from the original C0 input profile and the
original decomposition reserve, before the finite list or any later order. -/
theorem parameterRound2_original_germ_reserve_ball
    {J : Type*} [Fintype J]
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hLinear : IncrementsOriginalLinearSmoothInputs D)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs D)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs D rho)
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation D.atlas D.parameterChart
      D.sourceNormDomain D.parameterNormDomain D.parameterSet i))
    (ell ML : ℝ)
    (hProfile : incrementsOriginalInputProfileWithLinear D 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear D 0 ell).toReal ≤ ML) :
    let S := incrementsOriginalEvaluation D.atlas D.parameterChart
      D.sourceNormDomain D.parameterNormDomain D.parameterSet
    let W := incrementsOriginalParameterRegion D
    let p := parameterRound2_originalTensorGermSeminorm D.atlas D.parameterChart S W hS
      (fun _ _ hy => hy.1) ell
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional n‖*ML+1))
    0 < radius ∧ ∀ (H : parameterRound2_originalTensorGermSpace D.atlas D.parameterChart S W),
    H.val = D.H →
    ∀ (input : J → parameterRound2_originalTensorGermSpace D.atlas D.parameterChart S W),
    (∀ a, p 0 (input a-H) < radius) →
    ∃ G : Set (P × M), IsOpen G ∧ D.parameterSet ×ˢ (univ : Set M) ⊆ G ∧ G ⊆ W ∧
      (∀ a ν z, z ∈ G → z ∈ incrementsOriginalRelativeCutoffSupport D ν →
        rho/4 < D.linearArgument ν z.1 z.2 ((input a).val z.1 z.2)) ∧
      (∀ a z, z ∈ G → (input a).val z.1 z.2 =
        incrementsOriginalDecompositionTensor D z.1 z.2 ((input a).val z.1 z.2)) ∧
      (∀ a ν, ContMDiffOn
        ((𝓘(ℝ,EuclideanSpace ℝ (Fin d))).prod (𝓘(ℝ,EuclideanSpace ℝ (Fin n))))
        𝓘(ℝ,ℝ) ∞ (fun z : P × M => D.linearArgument ν z.1 z.2 ((input a).val z.1 z.2))
        (G ∩ D.primaryDomain ν)) := by
  intro S W p radius
  have hML0 : 0 ≤ ML := ENNReal.toReal_nonneg.trans hML
  have hr := original_reserve_radius_bound rho (‖actualOriginalCoefficientFunctional n‖*ML)
    hReserve.reserve_pos (mul_nonneg (actualOriginalCoefficientFunctional n).opNorm_nonneg hML0)
  refine ⟨hr.1,?_⟩
  intro H hH input hclose
  have hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation D.atlas D.parameterChart i :=
    fun _ _ hy => hy.1
  have hFinite (a : J) : paperAtlasCj 0
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => (input a).val p x-D.H p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart) S ≠ ⊤ := by
    have hh := parameterRound2_tensorGerm_weighted_finite D.atlas D.parameterChart S W hS hSO
      (input a-H) 0 0 ell
    change paperAtlasWeighted 0 0 ell
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => (input a).val p x-H.val p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart) S ≠ ⊤ at hh
    rw [hH] at hh
    simpa only [paperAtlasWeighted,zero_add,Finset.range_one,Finset.sum_singleton,pow_zero,one_mul] using hh
  have hR (a : J) : (paperAtlasCj 0
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => (input a).val p x-D.H p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart) S).toReal ≤ radius := by
    have hh := (hclose a).le
    change (paperAtlasWeighted 0 0 ell
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => (input a).val p x-H.val p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart) S).toReal ≤ radius at hh
    rw [hH] at hh
    simpa only [paperAtlasWeighted,zero_add,Finset.range_one,Finset.sum_singleton,pow_zero,one_mul] using hh
  exact parameterRound2_original_finite_joint_smooth_reserve_from_germ_inputs D hd hLinear hDecomp rho hReserve
    (fun a => (input a).val)
    (fun a p hp x => (input a).property.2 (p,x) ⟨hp,mem_univ _⟩)
    (fun a => (input a).property.1) ell ML radius hProfile hML hFinite hR hr.2

#print axioms parameterRound2_original_germ_reserve_ball
end GlobalEmbedding.Continuation
