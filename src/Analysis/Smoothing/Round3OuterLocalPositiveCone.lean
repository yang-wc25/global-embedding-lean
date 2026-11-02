import Smoothing.Round3OuterPositiveCone
import Smoothing.Round3OuterPositiveGermSamples

/-! The computed target gets a genuine positive-cone decomposition on one
open neighborhood of the compact parameter set. No global compactness of
parameter space and no membership in an old arbitrary fiber is assumed.
The neighborhood is chosen once, before all later derivative orders.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]
local notation "Dsource" => EuclideanSpace ℝ (Fin n)
local notation "IT" => 𝓘(ℝ,Dsource)

def round3OriginalLocalRetargetPositiveConeData
    (D : IncrementsOriginalNativeData n d N M P)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (U : Set P) (reserve : ℝ) : IncrementsOriginalNativeData n d N M P :=
  { D with
    parameterOpen := U
    H := T
    tensorNeighborhood := round3OriginalPositiveCone D reserve }

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem round3_original_local_retarget_positive_cone
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hD : IncrementsOriginalQualitativeDecompositionInputs D)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (hT : ∀ p ∈ D.parameterOpen, ∀ x, (T p x).IsSymm)
    (U : Set P) (hU : IsOpen U) (hKU : D.parameterSet ⊆ U) (hUW : U ⊆ D.parameterOpen)
    (reserve : ℝ) (hr : 0 < reserve)
    (hTpos : ∀ ν z, z.1 ∈ U → z ∈ incrementsOriginalRelativeCutoffSupport D ν →
      reserve < D.linearArgument ν z.1 z.2 (T z.1 z.2))
    (hRpos : ∀ ν z, z.1 ∈ U → z ∈ incrementsOriginalRelativeCutoffSupport D ν →
      reserve < D.linearArgument ν z.1 z.2 (D.reference z.1 z.2)) :
    IncrementsOriginalDomainConditions (round3OriginalLocalRetargetPositiveConeData D T U reserve) ∧
    IncrementsOriginalQualitativeDecompositionInputs
      (round3OriginalLocalRetargetPositiveConeData D T U reserve) ∧
    IncrementsOriginalDecompositionReserveInputs
      (round3OriginalLocalRetargetPositiveConeData D T U reserve) reserve := by
  let E := round3OriginalLocalRetargetPositiveConeData D T U reserve
  have hRel (ν : Fin D.primaryCount) : incrementsOriginalRelativeCutoffSupport E ν ⊆
      incrementsOriginalRelativeCutoffSupport D ν := by
    rw [parameterRound2_original_relativeSupport_eq E hU,
      parameterRound2_original_relativeSupport_eq D hd.parameter_open]
    intro z hz
    exact ⟨⟨hUW hz.1.1,hz.1.2⟩,hz.2⟩
  refine ⟨{ hd with
    parameter_open := hU
    parameter_subset := hKU
    cutoff_support_local := fun ν => (hRel ν).trans (hd.cutoff_support_local ν) },?_,?_⟩
  · refine { fiber_open := fun p _ x => round3_original_positive_cone_open D reserve p x
             H_symmetric := fun p hp x => hT p (hUW hp) x
             reference_symmetric := fun p hp x => hD.reference_symmetric p (hUW hp) x
             H_mem := ?_
             reference_mem := ?_
             decomposition := ?_
             argument_positive := ?_ }
    · intro p hp x ν hν
      exact hTpos ν (p,x) hp hν
    · intro p hp x ν hν
      exact hRpos ν (p,x) hp hν
    · intro p hp x A hA
      apply (incrementsOriginal_decomposition_extension D hD p (hUW hp) x).2 A
      intro ν hν
      have hrel : (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν := by
        rw [parameterRound2_original_relativeSupport_eq D hd.parameter_open]
        exact ⟨⟨hUW hp,mem_univ _⟩,subset_tsupport _ hν⟩
      exact (hr.trans (hA ν hrel)).le
    · intro p hp x ν hν A hA
      have hrel : (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν := by
        rw [parameterRound2_original_relativeSupport_eq D hd.parameter_open]
        exact ⟨⟨hUW hp,mem_univ _⟩,subset_tsupport _ hν⟩
      exact hr.trans (hA ν hrel)
  · refine ⟨hr,?_⟩
    intro ν z hz hp A hA
    exact (hA ν (hRel ν hz)).le

variable [CompactSpace M]

/-- Original C0 control of the actual computed target supplies every field of
its qualitative decomposition record and a fixed positive reserve near K.
The reference field and target are the same native tensors throughout. -/
theorem round3_original_local_retarget_positive_cone_of_C0
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hLinear : IncrementsOriginalLinearSmoothInputs D)
    (hD : IncrementsOriginalQualitativeDecompositionInputs D)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs D rho)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (hT : ∀ p ∈ D.parameterOpen, ∀ x, (T p x).IsSymm)
    (hInput : ∀ i, ∃ O : Set (Fin (n+d) → ℝ), IsOpen O ∧
      incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet i ⊆ O ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas D.parameterChart T i) O)
    (hReference : ∀ i, ∃ O : Set (Fin (n+d) → ℝ), IsOpen O ∧
      incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet i ⊆ O ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.reference i) O)
    (ell ML R : ℝ)
    (hProfile : incrementsOriginalInputProfileWithLinear D 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear D 0 ell).toReal ≤ ML)
    (hFinite : paperAtlasCj 0
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => T p x-D.H p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet) ≠ ⊤)
    (hR : (paperAtlasCj 0
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => T p x-D.H p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet)).toReal ≤ R)
    (hSmall : ‖actualOriginalCoefficientFunctional n‖ * ML * R ≤ rho/2) :
    ∃ U : Set P, IsOpen U ∧ D.parameterSet ⊆ U ∧ U ⊆ D.parameterOpen ∧
      IncrementsOriginalDomainConditions (round3OriginalLocalRetargetPositiveConeData D T U (rho/4)) ∧
      IncrementsOriginalQualitativeDecompositionInputs
        (round3OriginalLocalRetargetPositiveConeData D T U (rho/4)) ∧
      IncrementsOriginalDecompositionReserveInputs
        (round3OriginalLocalRetargetPositiveConeData D T U (rho/4)) (rho/4) := by
  have hsT := parameterRound2_original_reserve_of_C0 D hd hD rho hReserve T hT
    ell ML R hProfile hML hFinite hR hSmall
  let input : Bool → (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x) :=
    fun b => if b then T else D.reference
  have hSymm : ∀ b, ∀ p ∈ D.parameterOpen, ∀ x, (input b p x).IsSymm := by
    intro b
    cases b
    · exact hD.reference_symmetric
    · exact hT
  have hGerm : ∀ b i, ∃ O : Set (Fin (n+d) → ℝ), IsOpen O ∧
      incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet i ⊆ O ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (input b) i) O := by
    intro b
    cases b
    · exact hReference
    · exact hInput
  have hSample : ∀ b ν z, z ∈ incrementsOriginalRelativeCutoffSupport D ν →
      z.1 ∈ D.parameterSet → rho/2 ≤ D.linearArgument ν z.1 z.2 (input b z.1 z.2) := by
    intro b ν z hz hp
    cases b
    · have h := hReserve.lower ν z hz hp _
        (hD.reference_mem z.1 (hd.parameter_subset hp) z.2)
      exact (by linarith [hReserve.reserve_pos] : rho/2 ≤ rho).trans h
    · exact hsT ν z hz hp
  obtain ⟨G,hG,hKG,hGW,hpos⟩ := round3_original_finite_positive_joint_from_germ_samples
    D hd hLinear input hSymm hGerm rho hReserve.reserve_pos hSample
  obtain ⟨U,V,hU,-,hKU,hMV,hUV⟩ :=
    generalized_tube_lemma hd.parameter_compact isCompact_univ hG hKG
  let U0 := U ∩ D.parameterOpen
  have hU0 : IsOpen U0 := hU.inter hd.parameter_open
  have hKU0 : D.parameterSet ⊆ U0 := fun p hp => ⟨hKU hp,hd.parameter_subset hp⟩
  have hU0G : ∀ z : P × M, z.1 ∈ U0 → z ∈ G :=
    fun z hz => hUV ⟨hz.1,hMV (mem_univ z.2)⟩
  refine ⟨U0,hU0,hKU0,inter_subset_right,?_⟩
  exact round3_original_local_retarget_positive_cone D hd hD T hT U0 hU0 hKU0
    inter_subset_right (rho/4) (by linarith [hReserve.reserve_pos])
    (fun ν z hz hrel => hpos true ν z (hU0G z hz) hrel)
    (fun ν z hz hrel => hpos false ν z (hU0G z hz) hrel)

#print axioms round3_original_local_retarget_positive_cone
#print axioms round3_original_local_retarget_positive_cone_of_C0
end GlobalEmbedding.Continuation
