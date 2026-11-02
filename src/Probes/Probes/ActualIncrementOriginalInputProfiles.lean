import Probes.ActualIncrementOriginalCoordinateJets

/-! Direct suppliers for the Lcoord/Acoord interface shared by the actual
primary displacement and the actual mean. The fields are literal views of
the original linear functional and the original symmetric tensor. Original
weighted norms and genuine coordinate transition jets are the only budgets.
The original positive neighborhood supplies the reserve at the real samples. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem actual_original_linear_tensor_coordinate_profiles
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hLinear : IncrementsOriginalLinearSmoothInputs D)
    (input : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hInput : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart i ∩
        (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
          incrementsOriginalParameterRegion D))
    (hSymm : ∀ p x, (input p x).IsSymm)
    (j : ℕ) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (ell : ℝ) (hell : 0 < ell) (ML MA : ℝ)
    (hProfile : incrementsOriginalInputProfileWithLinear D j ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear D j ell).toReal ≤ ML)
    (hInputFinite : paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet) ≠ ⊤)
    (hMA : (paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet)).toReal ≤ MA)
    (ν : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount)
    (phi : X → Fin (n+d) → ℝ) (V R : Set X)
    (hV : IsOpen V) (hRV : R ⊆ V) (hphi : ContDiffOn ℝ ∞ phi V)
    (hmap : MapsTo phi V (incrementsOriginalPrimaryDifferentiation D ν i ∩
      (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
        incrementsOriginalParameterRegion D))
    (hsample : MapsTo phi R (incrementsOriginalPrimaryEvaluation D ν i))
    (hphijet : ∀ x ∈ R, ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1) * ‖iteratedFDeriv ℝ k phi x‖ ≤ T k) :
    let L := fun z => actualOriginalCoefficientFunctional n
      (incrementsOriginalLinearArgumentCoordinates D ν i (phi z))
    let A := incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i ∘ phi
    let C := actualFastChartTransferPrefix T j * coordinateDimensionFactor (n+d) j
    ContDiffOn ℝ ∞ L V ∧ ContDiffOn ℝ ∞ A V ∧
      (∀ z ∈ V, L z (A z) =
        D.linearArgument ν (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1
          (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).2
          (input (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1
            (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).2)) ∧
      (∀ k ≤ j, ∀ z ∈ R, ell^k * ‖iteratedFDeriv ℝ k L z‖ ≤
        ‖actualOriginalCoefficientFunctional n‖ * C * ML) ∧
      (∀ k ≤ j, ∀ z ∈ R, ell^k * ‖iteratedFDeriv ℝ k A z‖ ≤ C * MA) := by
  intro L A C
  let O := incrementsOriginalDifferentiation D.atlas D.parameterChart
  let S := incrementsOriginalEvaluation D.atlas D.parameterChart
    D.sourceNormDomain D.parameterNormDomain D.parameterSet
  let U := fun a => O a ∩ (incrementsOriginalJointPoint D.atlas D.parameterChart a) ⁻¹'
    incrementsOriginalParameterRegion D
  let OL := incrementsOriginalPrimaryDifferentiation D ν
  let SL := incrementsOriginalPrimaryEvaluation D ν
  let UL := fun a => OL a ∩ (incrementsOriginalJointPoint D.atlas D.parameterChart a) ⁻¹'
    incrementsOriginalParameterRegion D
  have hO : ∀ a, IsOpen (O a) := parameterRound2_originalDifferentiation_open D.atlas D.parameterChart
  have hU : ∀ a, IsOpen (U a) := actual_original_parameter_coordinate_region_open D hd.parameter_open
  have hSU : ∀ a, S a ⊆ U a := by
    intro a y hy
    exact ⟨hy.1, hd.parameter_subset hy.2.2.2, mem_univ _⟩
  have hOL : ∀ a, IsOpen (OL a) := actual_original_primaryDifferentiation_open D hd.primary_open ν
  have hUL : ∀ a, IsOpen (UL a) := by
    intro a
    exact ((actual_original_jointPoint_continuousOn D a).mono inter_subset_left).isOpen_inter_preimage
      (hOL a) (hd.parameter_open.prod isOpen_univ)
  have hSLUL : ∀ a, SL a ⊆ UL a := by
    intro a y hy
    exact ⟨⟨hy.1.1,hy.2⟩,hd.parameter_subset hy.1.2.2.2,mem_univ _⟩
  have hLinearLe : paperAtlasWeighted 0 j ell (incrementsOriginalLinearArgumentCoordinates D ν)
      OL SL ≤ incrementsOriginalInputProfileWithLinear D j ell :=
    (le_iSup (fun mu => paperAtlasWeighted 0 j ell
      (incrementsOriginalLinearArgumentCoordinates D mu)
      (incrementsOriginalPrimaryDifferentiation D mu)
      (incrementsOriginalPrimaryEvaluation D mu)) ν).trans (le_max_right _ _)
  have hLp := actual_original_weighted_coordinate_transfer j T hT ell hell
    (incrementsOriginalLinearArgumentCoordinates D ν) OL UL SL hOL hUL
    (fun _ => inter_subset_left) hSLUL (hLinear.linear_coordinates ν)
    (ne_top_of_le_ne_top hProfile hLinearLe) ML
    ((ENNReal.toReal_mono hProfile hLinearLe).trans hML)
    i phi V R hV hRV hphi hmap hsample hphijet
  have hAp := actual_original_weighted_coordinate_transfer j T hT ell hell
    (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input) O U S hO hU
    (fun _ => inter_subset_left) hSU hInput hInputFinite MA hMA
    i phi V R hV hRV hphi (fun z hz => ⟨(hmap hz).1.1,(hmap hz).2⟩)
    (fun z hz => (hsample hz).1) hphijet
  refine ⟨(actualOriginalCoefficientFunctional n).contDiff.comp_contDiffOn hLp.1,
    hAp.1, ?_, ?_, hAp.2⟩
  · intro z hz
    exact (actualOriginalCoefficientFunctional_apply n _ _).trans
      (actual_original_linear_argument_tensor_pairing D hd.atlas_smooth input ν i (phi z)
        (hmap hz).1.1.1 (hSymm _ _)).symm
  · intro k hk z hz
    have h := (actualOriginalCoefficientFunctional n).norm_iteratedFDeriv_comp_left
      (hLp.1.contDiffAt (hV.mem_nhds (hRV hz))) (by simp : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω))
    calc
      _ ≤ ell^k * (‖actualOriginalCoefficientFunctional n‖ *
          ‖iteratedFDeriv ℝ k (incrementsOriginalLinearArgumentCoordinates D ν i ∘ phi) z‖) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hell.le k)
      _ = ‖actualOriginalCoefficientFunctional n‖ * (ell^k *
          ‖iteratedFDeriv ℝ k (incrementsOriginalLinearArgumentCoordinates D ν i ∘ phi) z‖) := by ring
      _ ≤ ‖actualOriginalCoefficientFunctional n‖ *
          (actualFastChartTransferPrefix T j * coordinateDimensionFactor (n+d) j * ML) :=
        mul_le_mul_of_nonneg_left (hLp.2 k hk z hz) (actualOriginalCoefficientFunctional n).opNorm_nonneg
      _ = _ := by dsimp only [C]; ring

/-- The reserve comes from the SAME original positive neighborhood, only on
the genuine relative joint cutoff support over the parameter evaluation set. -/
theorem actual_original_coordinate_pairing_reserve
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (rho : ℝ)
    (hReserve : IncrementsOriginalDecompositionReserveInputs D rho)
    (input : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hSymm : ∀ p x, (input p x).IsSymm)
    (ν : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount)
    (y : Fin (n+d) → ℝ)
    (hy : y ∈ incrementsOriginalPrimaryEvaluation D ν i)
    (hsupport : incrementsOriginalJointPoint D.atlas D.parameterChart i y ∈
      incrementsOriginalRelativeCutoffSupport D ν)
    (hmem : (⟨input (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1
        (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2, hSymm _ _⟩) ∈
      D.tensorNeighborhood (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1
        (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2) :
    rho ≤ actualOriginalCoefficientFunctional n
      (incrementsOriginalLinearArgumentCoordinates D ν i y)
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i y) := by
  rw [actualOriginalCoefficientFunctional_apply,
    ← actual_original_linear_argument_tensor_pairing D hd.atlas_smooth input ν i y hy.1.1.1 (hSymm _ _)]
  exact hReserve.lower ν _ hsupport hy.1.2.2.2 _ hmem

/-- The difference budget is the original norm of the SAME native tensor
difference. The coordinate transition and derivative weights stay unchanged. -/
theorem actual_original_tensor_coordinate_difference_profile
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (input inputbar : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hInput : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart i ∩
        (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
          incrementsOriginalParameterRegion D))
    (hInputbar : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart inputbar i)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart i ∩
        (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
          incrementsOriginalParameterRegion D))
    (j : ℕ) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (ell : ℝ) (hell : 0 < ell) (Delta : ℝ)
    (hFinite : paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => input p x-inputbar p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet) ≠ ⊤)
    (hDelta : (paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => input p x-inputbar p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet)).toReal ≤ Delta)
    (i : Fin D.atlas.count × Fin D.parameterCount)
    (phi : X → Fin (n+d) → ℝ) (V R : Set X)
    (hV : IsOpen V) (hRV : R ⊆ V) (hphi : ContDiffOn ℝ ∞ phi V)
    (hmap : MapsTo phi V (incrementsOriginalDifferentiation D.atlas D.parameterChart i ∩
      (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
        incrementsOriginalParameterRegion D))
    (hsample : MapsTo phi R (incrementsOriginalEvaluation D.atlas D.parameterChart
      D.sourceNormDomain D.parameterNormDomain D.parameterSet i))
    (hphijet : ∀ x ∈ R, ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1) * ‖iteratedFDeriv ℝ k phi x‖ ≤ T k) :
    let diff := fun z => incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i (phi z) -
      incrementsOriginalTensorCoordinates D.atlas D.parameterChart inputbar i (phi z)
    ContDiffOn ℝ ∞ diff V ∧ ∀ k ≤ j, ∀ z ∈ R,
      ell^k * ‖iteratedFDeriv ℝ k diff z‖ ≤
        actualFastChartTransferPrefix T j * coordinateDimensionFactor (n+d) j * Delta := by
  let O := incrementsOriginalDifferentiation D.atlas D.parameterChart
  let S := incrementsOriginalEvaluation D.atlas D.parameterChart
    D.sourceNormDomain D.parameterNormDomain D.parameterSet
  let U := fun a => O a ∩ (incrementsOriginalJointPoint D.atlas D.parameterChart a) ⁻¹'
    incrementsOriginalParameterRegion D
  have hSU : ∀ a, S a ⊆ U a := by
    intro a y hy
    exact ⟨hy.1,hd.parameter_subset hy.2.2.2,mem_univ _⟩
  have heq (a) : incrementsOriginalTensorCoordinates D.atlas D.parameterChart
      (fun p x => input p x-inputbar p x) a = fun y =>
        incrementsOriginalTensorCoordinates D.atlas D.parameterChart input a y -
        incrementsOriginalTensorCoordinates D.atlas D.parameterChart inputbar a y := rfl
  have hdiff : ∀ a, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas D.parameterChart
      (fun p x => input p x-inputbar p x) a) (U a) := by
    intro a
    rw [heq a]
    exact (hInput a).sub (hInputbar a)
  exact actual_original_weighted_coordinate_transfer j T hT ell hell
    (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => input p x-inputbar p x))
    O U S (parameterRound2_originalDifferentiation_open D.atlas D.parameterChart)
    (actual_original_parameter_coordinate_region_open D hd.parameter_open)
    (fun _ => inter_subset_left) hSU hdiff hFinite Delta hDelta
    i phi V R hV hRV hphi hmap hsample hphijet

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_linear_tensor_coordinate_profiles
#print axioms GlobalEmbedding.Continuation.actual_original_coordinate_pairing_reserve
#print axioms GlobalEmbedding.Continuation.actual_original_tensor_coordinate_difference_profile
