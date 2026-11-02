import Smoothing.ParameterRound2OriginalArgumentGermProfiles

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

theorem parameterRound2_original_argument_difference_germ_profiles
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hLinear : IncrementsOriginalLinearSmoothInputs D)
    (input inputbar : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hInput : ∀ i, ∃ U : Set (Fin (n+d) → ℝ), IsOpen U ∧
      incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet i ⊆ U ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i) U)
    (hInputbar : ∀ i, ∃ U : Set (Fin (n+d) → ℝ), IsOpen U ∧
      incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet i ⊆ U ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas D.parameterChart inputbar i) U)
    (hSymm : ∀ p ∈ D.parameterOpen, ∀ x, (input p x).IsSymm)
    (hSymmbar : ∀ p ∈ D.parameterOpen, ∀ x, (inputbar p x).IsSymm)
    (j : ℕ) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (ell : ℝ) (hell : 0 < ell) (ML Delta : ℝ)
    (hProfile : incrementsOriginalInputProfileWithLinear D j ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear D j ell).toReal ≤ ML)
    (hDiffFinite : paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => input p x-inputbar p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet) ≠ ⊤)
    (hDelta : (paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => input p x-inputbar p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet)).toReal ≤ Delta)
    (ν : Fin D.primaryCount) (i : Fin D.atlas.count × Fin D.parameterCount)
    (phi : X → Fin (n+d) → ℝ) (V R : Set X)
    (hV : IsOpen V) (hRV : R ⊆ V) (hphi : ContDiffOn ℝ ∞ phi V)
    (hmap : MapsTo phi V (incrementsOriginalPrimaryDifferentiation D ν i ∩
      (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
        incrementsOriginalParameterRegion D))
    (hsample : MapsTo phi R (incrementsOriginalPrimaryEvaluation D ν i))
    (hphijet : ∀ x ∈ R, ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1) * ‖iteratedFDeriv ℝ k phi x‖ ≤ T k) :
    let arg := fun z =>
      D.linearArgument ν (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1
        (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).2
        (input (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1
          (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).2) -
      D.linearArgument ν (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1
        (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).2
        (inputbar (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1
          (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).2)
    let C := actualFastChartTransferPrefix T j * coordinateDimensionFactor (n+d) j
    ∃ V0 : Set X, IsOpen V0 ∧ R ⊆ V0 ∧ V0 ⊆ V ∧ ContDiffOn ℝ ∞ arg V0 ∧
      ∀ k ≤ j, ∀ z ∈ R, ell^k * ‖iteratedFDeriv ℝ k arg z‖ ≤
        2^j * (‖actualOriginalCoefficientFunctional n‖ * C * ML) * (C * Delta) := by
  intro arg C
  let diff := fun p x => input p x-inputbar p x
  have hDiff : ∀ a, ∃ UI : Set (Fin (n+d) → ℝ), IsOpen UI ∧
      incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet a ⊆ UI ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas D.parameterChart diff a) UI := by
    intro a
    obtain ⟨UA,hUA,hSA,hA⟩ := hInput a
    obtain ⟨UB,hUB,hSB,hB⟩ := hInputbar a
    exact ⟨UA ∩ UB,hUA.inter hUB,fun z hz => ⟨hSA hz,hSB hz⟩,
      (hA.mono inter_subset_left).sub (hB.mono inter_subset_right)⟩
  have hSymmDiff : ∀ p ∈ D.parameterOpen, ∀ x, (diff p x).IsSymm :=
    fun p hp x => (hSymm p hp x).sub (hSymmbar p hp x)
  have hh := parameterRound2_original_argument_germ_profiles D hd hLinear diff hDiff hSymmDiff
    j T hT ell hell ML Delta hProfile hML hDiffFinite hDelta
    ν i phi V R hV hRV hphi hmap hsample hphijet
  have heq : (fun z => D.linearArgument ν
      (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1
      (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).2
      (diff (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1
        (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).2)) = arg := by
    funext z
    exact map_sub (D.linearArgument ν
      (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1
      (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).2)
      (input (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1
        (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).2)
      (inputbar (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1
        (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).2)
  dsimp only at hh
  rw [heq] at hh
  exact hh

#print axioms parameterRound2_original_argument_difference_germ_profiles
end GlobalEmbedding.Continuation
