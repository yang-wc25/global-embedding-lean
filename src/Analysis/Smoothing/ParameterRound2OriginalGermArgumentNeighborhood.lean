import Smoothing.ParameterRound2OriginalGermArgumentSmooth

/-! Continuity of the original linear argument is derived from the original
symmetric coefficient and tensor coordinate fields. No native argument
regularity is added as an independent original input. -/

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

/-- A genuine joint open neighborhood of K times M on which every original
linear argument is smooth. It is built from the actual input coordinate germs,
using the original atlas cover. The neighborhood is independent of derivative
order; no common-open assumption is imposed on the entire reserve ball. -/
theorem parameterRound2_original_argument_germ_neighborhood
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hLinear : IncrementsOriginalLinearSmoothInputs D)
    (input : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x))
    (hSymm : ∀ p ∈ D.parameterOpen, ∀ x, (input p x).IsSymm)
    (hInput : ∀ i, ∃ U : Set (Fin (n+d) → ℝ), IsOpen U ∧
      incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet i ⊆ U ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i) U) :
    ∃ G : Set (P × M), IsOpen G ∧ D.parameterSet ×ˢ (univ : Set M) ⊆ G ∧
      G ⊆ incrementsOriginalParameterRegion D ∧
      ∀ ν, ContMDiffOn
        ((𝓘(ℝ,EuclideanSpace ℝ (Fin d))).prod (𝓘(ℝ,EuclideanSpace ℝ (Fin n))))
        𝓘(ℝ,ℝ) ∞ (fun z : P × M => D.linearArgument ν z.1 z.2 (input z.1 z.2))
        (G ∩ D.primaryDomain ν) := by
  classical
  choose UI hUI hSUI hInputUI using hInput
  let phi := parameterRound2_originalForwardCoordinates D
  let Src := fun i : Fin D.atlas.count × Fin D.parameterCount =>
    (D.parameterChart i.2).source ×ˢ (D.atlas.chart i.1).source
  let GI := fun i : Fin D.atlas.count × Fin D.parameterCount => Src i ∩ (phi i) ⁻¹' UI i
  have hSrc (i) : IsOpen (Src i) := (D.parameterChart i.2).open_source.prod (D.atlas.chart i.1).open_source
  have hphi (i) : ContinuousOn (phi i) (Src i) :=
    (parameterTensorModelEquiv n d).continuous.comp_continuousOn
      (((D.parameterChart i.2).continuousOn.comp continuousOn_fst (fun _ hz => hz.1)).prodMk
        ((D.atlas.chart i.1).continuousOn.comp continuousOn_snd (fun _ hz => hz.2)))
  have hGI (i) : IsOpen (GI i) := (hphi i).isOpen_inter_preimage (hSrc i) (hUI i)
  let G := incrementsOriginalParameterRegion D ∩ ⋃ i, GI i
  have hG : IsOpen G := (hd.parameter_open.prod isOpen_univ).inter (isOpen_iUnion hGI)
  have hKG : D.parameterSet ×ˢ (univ : Set M) ⊆ G := by
    intro z hz
    obtain ⟨a,ha⟩ := D.atlas.cover z.2
    obtain ⟨b,hb,hbn⟩ := hd.parameter_cover z.1 hz.1
    let i : Fin D.atlas.count × Fin D.parameterCount := (a,b)
    have hx : z.2 ∈ (D.atlas.chart i.1).source := D.atlas.inner_subset a ha
    have hp : z.1 ∈ (D.parameterChart i.2).source := hb
    have he := parameterRound2_originalForward_left_inv D i z hp hx
    have hm := parameterRound2_originalForward_mem D i z hp hx
    have hc := parameterRound2_originalForward_components D i z
    have hp' : incrementsOriginalParameterPoint (phi i z) = D.parameterChart i.2 z.1 := congrArg Prod.fst hc
    have hx' : incrementsOriginalSourcePoint (phi i z) = D.atlas.chart i.1 z.2 := congrArg Prod.snd hc
    have hy : phi i z ∈ incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet i := by
      refine ⟨hm,?_,?_,?_⟩
      · rw [hx']
        exact hd.source_inner_norm a z.2 ha
      · rw [hp']
        exact hbn
      · change (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi i z)).1 ∈ D.parameterSet
        rw [he]
        exact hz.1
    exact ⟨⟨hd.parameter_subset hz.1,mem_univ _⟩,mem_iUnion.mpr ⟨i,⟨hp,hx⟩,hSUI i hy⟩⟩
  refine ⟨G,hG,hKG,inter_subset_left,?_⟩
  intro ν z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz.1.2
  exact (parameterRound2_original_argument_contMDiffAt_of_coordinate_germ D hd hLinear input hSymm
    i (UI i) (hUI i) (hInputUI i) ν z hi.1.1 hi.1.2 hz.1.1 hz.2 hi.2).contMDiffWithinAt

#print axioms parameterRound2_original_argument_germ_neighborhood
end GlobalEmbedding.Continuation
