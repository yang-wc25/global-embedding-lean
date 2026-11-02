import Smoothing.ParameterRound2OriginalMeanInputProfiles
import Smoothing.ParameterRound2TensorGermSpace

/-! Original joint input profiles with symmetry required only on the original
parameter-open region. This preserves the actual original hypotheses; all
linear/tensor values and the full joint weighted norms are unchanged. -/

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

theorem parameterRound2_original_input_germ_profiles
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hLinear : IncrementsOriginalLinearSmoothInputs D)
    (input : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hInput : ∀ i, ∃ U : Set (Fin (n+d) → ℝ), IsOpen U ∧
      incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet i ⊆ U ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i) U)
    (hSymm : ∀ p ∈ D.parameterOpen, ∀ x, (input p x).IsSymm)
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
    ∃ V0 : Set X, IsOpen V0 ∧ R ⊆ V0 ∧ V0 ⊆ V ∧
      ContDiffOn ℝ ∞ L V0 ∧ ContDiffOn ℝ ∞ A V0 ∧
      (∀ z ∈ V0, L z (A z) =
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
  let U := fun a => O a ∩ Classical.choose (hInput a)
  let OL := incrementsOriginalPrimaryDifferentiation D ν
  let SL := incrementsOriginalPrimaryEvaluation D ν
  let UL := fun a => OL a ∩ (incrementsOriginalJointPoint D.atlas D.parameterChart a) ⁻¹'
    incrementsOriginalParameterRegion D
  have hO : ∀ a, IsOpen (O a) := parameterRound2_originalDifferentiation_open D.atlas D.parameterChart
  have hU : ∀ a, IsOpen (U a) := fun a => (hO a).inter (Classical.choose_spec (hInput a)).1
  have hSU : ∀ a, S a ⊆ U a := fun a y hy => ⟨hy.1,(Classical.choose_spec (hInput a)).2.1 hy⟩
  have hInputU : ∀ a, ContDiffOn ℝ ∞
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input a) (U a) :=
    fun a => (Classical.choose_spec (hInput a)).2.2.mono inter_subset_right
  let V0 := V ∩ phi ⁻¹' U i
  have hV0 : IsOpen V0 := hphi.continuousOn.isOpen_inter_preimage hV (hU i)
  have hRV0 : R ⊆ V0 := fun z hz => ⟨hRV hz,hSU i (hsample hz).1⟩
  have hphi0 : ContDiffOn ℝ ∞ phi V0 := hphi.mono inter_subset_left
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
    i phi V0 R hV0 hRV0 hphi0 (fun z hz => hmap hz.1) hsample hphijet
  have hAp := actual_original_weighted_coordinate_transfer j T hT ell hell
    (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input) O U S hO hU
    (fun _ => inter_subset_left) hSU hInputU hInputFinite MA hMA
    i phi V0 R hV0 hRV0 hphi0 (fun z hz => hz.2)
    (fun z hz => (hsample hz).1) hphijet
  refine ⟨V0,hV0,hRV0,inter_subset_left,
    (actualOriginalCoefficientFunctional n).contDiff.comp_contDiffOn hLp.1,
    hAp.1, ?_, ?_, hAp.2⟩
  · intro z hz
    exact (actualOriginalCoefficientFunctional_apply n _ _).trans
      (actual_original_linear_argument_tensor_pairing D hd.atlas_smooth input ν i (phi z)
        (hmap hz.1).1.1.1 (hSymm _ (hmap hz.1).2.1 _)).symm
  · intro k hk z hz
    have h := (actualOriginalCoefficientFunctional n).norm_iteratedFDeriv_comp_left
      (hLp.1.contDiffAt (hV0.mem_nhds (hRV0 hz))) (by simp : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω))
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


#print axioms parameterRound2_original_input_germ_profiles
end GlobalEmbedding.Continuation
