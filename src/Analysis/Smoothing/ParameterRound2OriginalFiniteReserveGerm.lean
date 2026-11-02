import Smoothing.ParameterRound2OriginalReserveC0
import GlobalEmbedding.Paper.IncrementsOriginalDecompositionExtension
import Mathlib.Topology.Compactness.Compact

/-! A finite construction needs positivity only near the compact parameter
set. The same finite collection of actual native tensor inputs has one open
parameter neighborhood with a positive reserve. The neighborhood is chosen
once after the finite collection and before any later derivative order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem parameterRound2_original_relativeSupport_eq
    (D : IncrementsOriginalNativeData n d N M P)
    (hOpen : IsOpen D.parameterOpen) (ν : Fin D.primaryCount) :
    incrementsOriginalRelativeCutoffSupport D ν =
      incrementsOriginalParameterRegion D ∩ tsupport (D.cutoff ν) := by
  let W := incrementsOriginalParameterRegion D
  have hW : IsOpen W := hOpen.prod isOpen_univ
  unfold incrementsOriginalRelativeCutoffSupport
  change Subtype.val '' closure (Subtype.val ⁻¹' Function.support (D.cutoff ν) : Set W) =
    W ∩ closure (Function.support (D.cutoff ν))
  rw [← hW.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val (Function.support (D.cutoff ν)),Set.image_preimage_eq_inter_range]
  simp only [Subtype.range_coe_subtype,Set.ofPred_mem_eq,Set.inter_comm]

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- The finite list has one actual open parameter neighborhood. Only
continuity of its original linear arguments and the reserve over K enter.
No control outside K is inferred from the original norm. -/
theorem parameterRound2_original_finite_positive_joint_neighborhood
    {J : Type*} [Fintype J]
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (input : J → (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x))
    (hArg : ∀ a ν, ContinuousOn
      (fun z : P × M => D.linearArgument ν z.1 z.2 (input a z.1 z.2))
      (incrementsOriginalParameterRegion D ∩ D.primaryDomain ν))
    (rho : ℝ) (hrho : 0 < rho)
    (hSample : ∀ a ν z, z ∈ incrementsOriginalRelativeCutoffSupport D ν →
      z.1 ∈ D.parameterSet → rho/2 ≤ D.linearArgument ν z.1 z.2 (input a z.1 z.2)) :
    ∃ G : Set (P × M), IsOpen G ∧ D.parameterSet ×ˢ (univ : Set M) ⊆ G ∧
      G ⊆ incrementsOriginalParameterRegion D ∧
      ∀ a ν z, z ∈ G → z ∈ incrementsOriginalRelativeCutoffSupport D ν →
        rho/4 < D.linearArgument ν z.1 z.2 (input a z.1 z.2) := by
  classical
  let W := incrementsOriginalParameterRegion D
  have hW : IsOpen W := hd.parameter_open.prod isOpen_univ
  let good : J → Fin D.primaryCount → Set (P × M) := fun a ν =>
    (W \ tsupport (D.cutoff ν)) ∪
      ((W ∩ D.primaryDomain ν) ∩
        (fun z : P × M => D.linearArgument ν z.1 z.2 (input a z.1 z.2)) ⁻¹' Ioi (rho/4))
  have hgood : ∀ a ν, IsOpen (good a ν) := by
    intro a ν
    exact (hW.inter (isClosed_tsupport _).isOpen_compl).union
      ((hArg a ν).isOpen_inter_preimage (hW.inter (hd.primary_open ν)) isOpen_Ioi)
  let G : Set (P × M) := W ∩ ⋂ a, ⋂ ν, good a ν
  have hG : IsOpen G := hW.inter (isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun ν => hgood a ν)
  have hKG : D.parameterSet ×ˢ (univ : Set M) ⊆ G := by
    intro z hz
    have hzW : z ∈ W := ⟨hd.parameter_subset hz.1,mem_univ _⟩
    refine ⟨hzW,mem_iInter.mpr fun a => mem_iInter.mpr fun ν => ?_⟩
    by_cases hs : z ∈ tsupport (D.cutoff ν)
    · have hrel : z ∈ incrementsOriginalRelativeCutoffSupport D ν := by
        rw [parameterRound2_original_relativeSupport_eq D hd.parameter_open]
        exact ⟨hzW,hs⟩
      exact Or.inr ⟨⟨hzW,hd.cutoff_support_local ν hrel⟩,
        lt_of_lt_of_le (by linarith : rho/4 < rho/2) (hSample a ν z hrel hz.1)⟩
    · exact Or.inl ⟨hzW,hs⟩
  refine ⟨G,hG,hKG,inter_subset_left,?_⟩
  intro a ν z hzG hrel
  have hzGood := mem_iInter.mp (mem_iInter.mp hzG.2 a) ν
  rcases hzGood with hn | hp
  · have hs := (parameterRound2_original_relativeSupport_eq D hd.parameter_open ν) ▸ hrel
    exact (hn.2 hs.2).elim
  · exact hp.2

variable [CompactSpace M]

/-- Compact-source repair specialization of the genuine joint neighborhood.
The tube lemma produces one product parameter neighborhood; standalone
increments on a noncompact source instead uses the preceding joint version. -/
theorem parameterRound2_original_finite_positive_neighborhood
    {J : Type*} [Fintype J]
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (input : J → (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x))
    (hArg : ∀ a ν, ContinuousOn
      (fun z : P × M => D.linearArgument ν z.1 z.2 (input a z.1 z.2))
      (incrementsOriginalParameterRegion D ∩ D.primaryDomain ν))
    (rho : ℝ) (hrho : 0 < rho)
    (hSample : ∀ a ν z, z ∈ incrementsOriginalRelativeCutoffSupport D ν →
      z.1 ∈ D.parameterSet → rho/2 ≤ D.linearArgument ν z.1 z.2 (input a z.1 z.2)) :
    ∃ U : Set P, IsOpen U ∧ D.parameterSet ⊆ U ∧ U ⊆ D.parameterOpen ∧
      ∀ a ν z, z.1 ∈ U → z ∈ incrementsOriginalRelativeCutoffSupport D ν →
        rho/4 < D.linearArgument ν z.1 z.2 (input a z.1 z.2) := by
  obtain ⟨G,hG,hKG,hGW,hpos⟩ :=
    parameterRound2_original_finite_positive_joint_neighborhood D hd input hArg rho hrho hSample
  obtain ⟨U,V,hU,-,hKU,hMV,hUV⟩ :=
    generalized_tube_lemma hd.parameter_compact isCompact_univ hG hKG
  refine ⟨U ∩ D.parameterOpen,hU.inter hd.parameter_open,
    fun p hp => ⟨hKU hp,hd.parameter_subset hp⟩,inter_subset_right,?_⟩
  intro a ν z hz hrel
  exact hpos a ν z (hUV ⟨hz.1,hMV (mem_univ z.2)⟩) hrel

/-- Same actual finite tensor list, original C0 norms and original reserve:
the common open neighborhood and literal square-root decomposition are both
outputs. The new neighborhood can depend on this finite list, never on a
later derivative order. No computed input is assumed in tensorNeighborhood. -/
theorem parameterRound2_original_finite_reserve_decomposition_of_C0
    {J : Type*} [Fintype J]
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs D)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs D rho)
    (input : J → (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x))
    (hSymm : ∀ a, ∀ p ∈ D.parameterOpen, ∀ x, (input a p x).IsSymm)
    (hArg : ∀ a ν, ContinuousOn
      (fun z : P × M => D.linearArgument ν z.1 z.2 (input a z.1 z.2))
      (incrementsOriginalParameterRegion D ∩ D.primaryDomain ν))
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
    ∃ U : Set P, IsOpen U ∧ D.parameterSet ⊆ U ∧ U ⊆ D.parameterOpen ∧
      (∀ a ν z, z.1 ∈ U → z ∈ incrementsOriginalRelativeCutoffSupport D ν →
        rho/4 < D.linearArgument ν z.1 z.2 (input a z.1 z.2)) ∧
      (∀ a, ∀ p ∈ U, ∀ x, input a p x = incrementsOriginalDecompositionTensor D p x (input a p x)) := by
  have hs := fun a => parameterRound2_original_reserve_of_C0 D hd hDecomp rho hReserve
    (input a) (hSymm a) ell ML R hProfile hML (hFinite a) (hR a) hSmall
  obtain ⟨U,hU,hKU,hUW,hpos⟩ := parameterRound2_original_finite_positive_neighborhood
    D hd input hArg rho hReserve.reserve_pos hs
  refine ⟨U,hU,hKU,hUW,hpos,?_⟩
  intro a p hp x
  apply (incrementsOriginal_decomposition_extension D hDecomp p (hUW hp) x).2
    ⟨input a p x,hSymm a p (hUW hp) x⟩
  intro ν hν
  have hrel : (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν := by
    rw [parameterRound2_original_relativeSupport_eq D hd.parameter_open]
    exact ⟨⟨hUW hp,mem_univ _⟩,subset_tsupport _ hν⟩
  exact le_of_lt ((div_pos hReserve.reserve_pos (by norm_num : (0:ℝ)<4)).trans
    (hpos a ν (p,x) hp hrel))

#print axioms parameterRound2_original_finite_positive_joint_neighborhood
#print axioms parameterRound2_original_finite_positive_neighborhood
#print axioms parameterRound2_original_finite_reserve_decomposition_of_C0
end GlobalEmbedding.Continuation
