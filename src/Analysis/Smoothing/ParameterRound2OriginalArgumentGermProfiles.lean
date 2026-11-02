import Smoothing.ParameterRound2OriginalGermInputProfiles
import Smoothing.WeightedActualOperations

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

theorem parameterRound2_original_argument_germ_profiles
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
    let arg := fun z => D.linearArgument ν
      (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1
      (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).2
      (input (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1
        (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).2)
    let C := actualFastChartTransferPrefix T j * coordinateDimensionFactor (n+d) j
    ∃ V0 : Set X, IsOpen V0 ∧ R ⊆ V0 ∧ V0 ⊆ V ∧ ContDiffOn ℝ ∞ arg V0 ∧
      ∀ k ≤ j, ∀ z ∈ R, ell^k * ‖iteratedFDeriv ℝ k arg z‖ ≤
        2^j * (‖actualOriginalCoefficientFunctional n‖ * C * ML) * (C * MA) := by
  intro arg C
  obtain ⟨V0,hV0,hRV0,hV0V,hL,hA,hRep,hLb,hAb⟩ :=
    parameterRound2_original_input_germ_profiles D hd hLinear input hInput hSymm
      j T hT ell hell ML MA hProfile hML hInputFinite hMA
      ν i phi V R hV hRV hphi hmap hsample hphijet
  let L := fun z => actualOriginalCoefficientFunctional n
    (incrementsOriginalLinearArgumentCoordinates D ν i (phi z))
  let A := incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i ∘ phi
  have hProd : ContDiffOn ℝ ∞ (fun z => L z (A z)) V0 := hL.clm_apply hA
  have hArg : ContDiffOn ℝ ∞ arg V0 := hProd.congr (fun z hz => (hRep z hz).symm)
  refine ⟨V0,hV0,hRV0,hV0V,hArg,?_⟩
  intro k hk z hz
  have hh := scaled_clm_apply V0 hV0 L A hL hA k 0 ell
    (‖actualOriginalCoefficientFunctional n‖ * C * ML) (C*MA) hell.le
    (fun r hr => hLb r (hr.trans hk) z hz)
    (fun r hr => by simpa only [Nat.add_zero] using hAb r (hr.trans hk) z hz) (hRV0 hz)
  have he : (fun w => L w (A w)) =ᶠ[𝓝 z] arg := by
    filter_upwards [hV0.mem_nhds (hRV0 hz)] with w hw
    exact hRep w hw
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds] at hh
  simp only [Nat.add_zero] at hh
  have hC : 0 ≤ C := mul_nonneg (actualFastChartTransferPrefix_nonneg T hT j)
    (coordinateDimensionFactor_nonneg (n+d) j)
  have hML0 : 0 ≤ ML := ENNReal.toReal_nonneg.trans hML
  have hMA0 : 0 ≤ MA := ENNReal.toReal_nonneg.trans hMA
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC hMA0)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hk)
    (mul_nonneg (mul_nonneg (actualOriginalCoefficientFunctional n).opNorm_nonneg hC) hML0)

#print axioms parameterRound2_original_argument_germ_profiles
end GlobalEmbedding.Continuation
