import Smoothing.ParameterRound2OriginalObserverArgument

/-! The same literal observer argument difference, from the original tensor
paper norm. No derivative budget for the scalar difference is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "X" => Ep × Es

theorem parameterRound2_original_observer_argument_difference_germ_profiles
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (hInput : ∀ a, ∃ UI : Set (Fin (n+d) → ℝ), IsOpen UI ∧
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet a ⊆ UI ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart input a) UI)
    (hInputbar : ∀ a, ∃ UI : Set (Fin (n+d) → ℝ), IsOpen UI ∧
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet a ⊆ UI ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart inputbar a) UI)
    (hSymm : ∀ p ∈ Data.parameterOpen, ∀ x, (input p x).IsSymm)
    (hSymmbar : ∀ p ∈ Data.parameterOpen, ∀ x, (inputbar p x).IsSymm)
    (j : ℕ) (ell ML Delta : ℝ) (hell : 0 < ell)
    (hProfile : incrementsOriginalInputProfileWithLinear Data j ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear Data j ell).toReal ≤ ML)
    (hDiffFinite : paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input p x-inputbar p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) ≠ ⊤)
    (hDelta : (paperAtlasWeighted 0 j ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input p x-inputbar p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)).toReal ≤ Delta)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    let a := parameterTensorModelEquiv n d
    let C := actualFastChartTransferPrefix (fun _ => ‖a.toContinuousLinearMap‖) j *
      coordinateDimensionFactor (n+d) j
    let arg := fun z : X =>
      Data.linearArgument nu ((Data.parameterChart i.2).symm z.1) ((Data.atlas.chart i.1).symm z.2)
        (input ((Data.parameterChart i.2).symm z.1) ((Data.atlas.chart i.1).symm z.2)) -
      Data.linearArgument nu ((Data.parameterChart i.2).symm z.1) ((Data.atlas.chart i.1).symm z.2)
        (inputbar ((Data.parameterChart i.2).symm z.1) ((Data.atlas.chart i.1).symm z.2))
    ∃ V0 : Set X, IsOpen V0 ∧
      a ⁻¹' incrementsOriginalPrimaryEvaluation Data nu i ⊆ V0 ∧
      V0 ⊆ actualOriginalPrimaryNativeOpen Data nu i ∧ ContDiffOn ℝ ∞ arg V0 ∧
      ∀ k ≤ j, ∀ z, a z ∈ incrementsOriginalPrimaryEvaluation Data nu i →
        ell^k*‖iteratedFDeriv ℝ k arg z‖ ≤ 2^j*(‖actualOriginalCoefficientFunctional n‖*C*ML)*(C*Delta) := by
  intro a C arg
  let diff := fun p x => input p x-inputbar p x
  have hDiff : ∀ a, ∃ UI : Set (Fin (n+d) → ℝ), IsOpen UI ∧
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet a ⊆ UI ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart diff a) UI := by
    intro a
    obtain ⟨UA,hUA,hSA,hA⟩ := hInput a
    obtain ⟨UB,hUB,hSB,hB⟩ := hInputbar a
    exact ⟨UA ∩ UB,hUA.inter hUB,fun z hz => ⟨hSA hz,hSB hz⟩,
      (hA.mono inter_subset_left).sub (hB.mono inter_subset_right)⟩
  have hSymmDiff : ∀ p ∈ Data.parameterOpen, ∀ x, (diff p x).IsSymm :=
    fun p hp x => (hSymm p hp x).sub (hSymmbar p hp x)
  have hh := parameterRound2_original_observer_argument_germ_profiles Data hd hLinear
    diff hDiff hSymmDiff j ell ML Delta hell hProfile hML hDiffFinite hDelta nu i
  have heq : (fun z : X => Data.linearArgument nu ((Data.parameterChart i.2).symm z.1)
      ((Data.atlas.chart i.1).symm z.2)
      (diff ((Data.parameterChart i.2).symm z.1) ((Data.atlas.chart i.1).symm z.2))) = arg := by
    funext z
    exact map_sub (Data.linearArgument nu ((Data.parameterChart i.2).symm z.1) ((Data.atlas.chart i.1).symm z.2))
      (input ((Data.parameterChart i.2).symm z.1) ((Data.atlas.chart i.1).symm z.2))
      (inputbar ((Data.parameterChart i.2).symm z.1) ((Data.atlas.chart i.1).symm z.2))
  dsimp only at hh
  rw [heq] at hh
  exact hh

#print axioms parameterRound2_original_observer_argument_difference_germ_profiles
end GlobalEmbedding.Continuation
