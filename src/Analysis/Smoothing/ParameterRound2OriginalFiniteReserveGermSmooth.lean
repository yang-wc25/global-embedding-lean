import Smoothing.ParameterRound2OriginalFiniteReserveGermInputs
import Smoothing.ParameterRound2OriginalGermArgumentNeighborhood

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

theorem parameterRound2_original_finite_joint_smooth_reserve_from_germ_inputs
    {J : Type*} [Fintype J]
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hLinear : IncrementsOriginalLinearSmoothInputs D)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs D)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs D rho)
    (input : J → (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x))
    (hSymm : ∀ a, ∀ p ∈ D.parameterOpen, ∀ x, (input a p x).IsSymm)
    (hInput : ∀ a i, ∃ U : Set (Fin (n+d) → ℝ), IsOpen U ∧
      incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet i ⊆ U ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (input a) i) U)
    (ell ML R : ℝ)
    (hProfile : incrementsOriginalInputProfileWithLinear D 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear D 0 ell).toReal ≤ ML)
    (hFinite : ∀ a, paperAtlasCj 0
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => input a p x-D.H p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet) ≠ ⊤)
    (hR : ∀ a, (paperAtlasCj 0
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => input a p x-D.H p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet)).toReal ≤ R)
    (hSmall : ‖actualOriginalCoefficientFunctional n‖ * ML * R ≤ rho/2) :
    ∃ G : Set (P × M), IsOpen G ∧ D.parameterSet ×ˢ (univ : Set M) ⊆ G ∧
      G ⊆ incrementsOriginalParameterRegion D ∧
      (∀ a ν z, z ∈ G → z ∈ incrementsOriginalRelativeCutoffSupport D ν →
        rho/4 < D.linearArgument ν z.1 z.2 (input a z.1 z.2)) ∧
      (∀ a z, z ∈ G → input a z.1 z.2 =
        incrementsOriginalDecompositionTensor D z.1 z.2 (input a z.1 z.2)) ∧
      (∀ a ν, ContMDiffOn
        ((𝓘(ℝ,EuclideanSpace ℝ (Fin d))).prod (𝓘(ℝ,EuclideanSpace ℝ (Fin n))))
        𝓘(ℝ,ℝ) ∞ (fun z : P × M => D.linearArgument ν z.1 z.2 (input a z.1 z.2))
        (G ∩ D.primaryDomain ν)) := by
  classical
  obtain ⟨GP,hGP,hKGP,hGPW,hpos,hdec⟩ :=
    parameterRound2_original_finite_joint_reserve_from_germ_inputs D hd hLinear hDecomp rho hReserve
      input hSymm hInput ell ML R hProfile hML hFinite hR hSmall
  choose GS hGS hKGS hGSW hreg using
    fun a => parameterRound2_original_argument_germ_neighborhood D hd hLinear (input a) (hSymm a) (hInput a)
  let G := GP ∩ ⋂ a, GS a
  have hG : IsOpen G := hGP.inter (isOpen_iInter_of_finite hGS)
  have hKG : D.parameterSet ×ˢ (univ : Set M) ⊆ G := by
    intro z hz
    exact ⟨hKGP hz,mem_iInter.mpr (fun a => hKGS a hz)⟩
  refine ⟨G,hG,hKG,fun z hz => hGPW hz.1,?_,?_,?_⟩
  · intro a ν z hz hrel
    exact hpos a ν z hz.1 hrel
  · intro a z hz
    exact hdec a z hz.1
  · intro a ν
    exact (hreg a ν).mono (fun z hz => ⟨mem_iInter.mp hz.1.2 a,hz.2⟩)

#print axioms parameterRound2_original_finite_joint_smooth_reserve_from_germ_inputs
end GlobalEmbedding.Continuation
