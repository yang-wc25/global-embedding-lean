import Smoothing.ParameterRound2OriginalGermArgumentContinuity
import Smoothing.ParameterRound2OriginalFiniteReserveGerm

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

theorem parameterRound2_original_finite_joint_reserve_from_germ_inputs
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
        incrementsOriginalDecompositionTensor D z.1 z.2 (input a z.1 z.2)) := by
  classical
  have hs := fun a => parameterRound2_original_reserve_of_C0 D hd hDecomp rho hReserve
    (input a) (hSymm a) ell ML R hProfile hML (hFinite a) (hR a) hSmall
  let W := incrementsOriginalParameterRegion D
  let Good : Set (P × M) := {z | z ∈ W ∧ ∀ a ν, z ∈ tsupport (D.cutoff ν) →
    rho/4 < D.linearArgument ν z.1 z.2 (input a z.1 z.2)}
  let G := interior Good
  have hGW : G ⊆ W := fun z hz => (interior_subset hz).1
  have hKG : D.parameterSet ×ˢ (univ : Set M) ⊆ G := by
    intro z hz
    have hzW : z ∈ W := ⟨hd.parameter_subset hz.1,mem_univ _⟩
    have heach (a : J) (ν : Fin D.primaryCount) :
        ∀ᶠ w in 𝓝 z, w ∈ tsupport (D.cutoff ν) →
          rho/4 < D.linearArgument ν w.1 w.2 (input a w.1 w.2) := by
      by_cases hcut : z ∈ tsupport (D.cutoff ν)
      · have hrel : z ∈ incrementsOriginalRelativeCutoffSupport D ν := by
          rw [parameterRound2_original_relativeSupport_eq D hd.parameter_open]
          exact ⟨hzW,hcut⟩
        have hcont := parameterRound2_original_argument_germ_continuousAt D hd hLinear
          (input a) (hInput a) (hSymm a) ν z hz.1 (hd.cutoff_support_local ν hrel)
        have hm : rho/4 < D.linearArgument ν z.1 z.2 (input a z.1 z.2) :=
          lt_of_lt_of_le (by have := hReserve.reserve_pos; linarith) (hs a ν z hrel hz.1)
        filter_upwards [hcont.tendsto.eventually (isOpen_Ioi.mem_nhds hm)] with w hw
        exact fun _ => hw
      · filter_upwards [(isClosed_tsupport (D.cutoff ν)).isOpen_compl.mem_nhds hcut] with w hw
        exact fun h => (hw h).elim
    apply mem_interior_iff_mem_nhds.mpr
    have hall : ∀ᶠ w in 𝓝 z, ∀ a ν, w ∈ tsupport (D.cutoff ν) →
        rho/4 < D.linearArgument ν w.1 w.2 (input a w.1 w.2) :=
      eventually_all.mpr fun a => eventually_all.mpr (heach a)
    filter_upwards [(hd.parameter_open.prod isOpen_univ).mem_nhds hzW,hall] with w hw hpos
    exact ⟨hw,hpos⟩
  have hpos : ∀ a ν z, z ∈ G → z ∈ incrementsOriginalRelativeCutoffSupport D ν →
      rho/4 < D.linearArgument ν z.1 z.2 (input a z.1 z.2) := by
    intro a ν z hz hrel
    have hh := (parameterRound2_original_relativeSupport_eq D hd.parameter_open ν) ▸ hrel
    exact (interior_subset hz).2 a ν hh.2
  refine ⟨G,isOpen_interior,hKG,hGW,hpos,?_⟩
  intro a z hz
  apply (incrementsOriginal_decomposition_extension D hDecomp z.1 (hGW hz).1 z.2).2
    ⟨input a z.1 z.2,hSymm a z.1 (hGW hz).1 z.2⟩
  intro ν hν
  have hrel : z ∈ incrementsOriginalRelativeCutoffSupport D ν := by
    rw [parameterRound2_original_relativeSupport_eq D hd.parameter_open]
    exact ⟨hGW hz,subset_tsupport _ hν⟩
  exact le_of_lt ((div_pos hReserve.reserve_pos (by norm_num : (0:ℝ)<4)).trans
    (hpos a ν z hz hrel))

#print axioms parameterRound2_original_finite_joint_reserve_from_germ_inputs
end GlobalEmbedding.Continuation
