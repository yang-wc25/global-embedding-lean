import Smoothing.ParameterRound2OriginalHostArgument

/-! The same constructed host inverse pulls the literal original cutoff and
normal Core entries to the actual family. All estimates retain original
samples; actual open domains supply only qualitative differentiation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es

theorem parameterRound2_original_host_argument_difference_germ_profiles
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (j : ℕ)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (hInput : ∀ a, ∃ UI : Set (Fin (m+1+d) → ℝ), IsOpen UI ∧
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet a ⊆ UI ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart input a) UI)
    (hInputbar : ∀ a, ∃ UI : Set (Fin (m+1+d) → ℝ), IsOpen UI ∧
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet a ⊆ UI ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart inputbar a) UI)
    (hSymm : ∀ p ∈ Data.parameterOpen, ∀ x, (input p x).IsSymm)
    (hSymmbar : ∀ p ∈ Data.parameterOpen, ∀ x, (inputbar p x).IsSymm)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M Es)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) e)
    (S : Set X) (hS : S ⊆ b.target)
    (hsource : b.source ⊆ actualOriginalNativeOpen Data i)
    (hsample : MapsTo b.symm S ((parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (hprimary : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
      ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain nu)
    (ell ML Delta : ℝ) (hell : 0 < ell)
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
    (hinvjet : ∀ k, 1 ≤ k → k ≤ j → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k b.symm z‖ ≤ T k) :
    let a := parameterTensorModelEquiv (m+1) d
    let C := actualFastChartTransferPrefix (fun k => ‖a.toContinuousLinearMap‖*T k) j *
      coordinateDimensionFactor (m+1+d) j
    let arg := fun z : X =>
      Data.linearArgument nu ((Data.parameterChart i.2).symm z.1)
        ((e z.1).symm z.2) (input ((Data.parameterChart i.2).symm z.1) ((e z.1).symm z.2)) -
      Data.linearArgument nu ((Data.parameterChart i.2).symm z.1)
        ((e z.1).symm z.2) (inputbar ((Data.parameterChart i.2).symm z.1) ((e z.1).symm z.2))
    ∃ V0 : Set X, IsOpen V0 ∧ S ⊆ V0 ∧ V0 ⊆ b.target ∧ ContDiffOn ℝ ∞ arg V0 ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k arg z‖ ≤
        2^j*(‖actualOriginalCoefficientFunctional (m+1)‖*C*ML)*(C*Delta) := by
  intro a C arg
  let diff := fun p x => input p x-inputbar p x
  have hDiff : ∀ a, ∃ UI : Set (Fin (m+1+d) → ℝ), IsOpen UI ∧
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
  have hh := parameterRound2_original_host_argument_germ_profiles T hT j Data hd hLinear
    diff hDiff hSymmDiff i nu b e hdata S hS hsource hsample hprimary ell ML Delta hell
    hProfile hML hDiffFinite hDelta hinvjet
  have heq : (fun z : X => Data.linearArgument nu ((Data.parameterChart i.2).symm z.1)
      ((e z.1).symm z.2) (diff ((Data.parameterChart i.2).symm z.1) ((e z.1).symm z.2))) = arg := by
    funext z
    exact map_sub (Data.linearArgument nu ((Data.parameterChart i.2).symm z.1) ((e z.1).symm z.2))
      (input ((Data.parameterChart i.2).symm z.1) ((e z.1).symm z.2))
      (inputbar ((Data.parameterChart i.2).symm z.1) ((e z.1).symm z.2))
  dsimp only at hh
  rw [heq] at hh
  exact hh

#print axioms parameterRound2_original_host_argument_difference_germ_profiles
end GlobalEmbedding.Continuation
