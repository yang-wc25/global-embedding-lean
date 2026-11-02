import Smoothing.ParameterRound2OriginalArgumentContinuity
import Smoothing.ParameterRound2TensorGermSpace

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

/-- The native argument is actually continuous at every relevant point over
K, using only original coordinate smoothness. This suffices to create the
finite common positivity germ; no coordinate budget is used off K. -/
theorem parameterRound2_original_argument_germ_continuousAt
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hLinear : IncrementsOriginalLinearSmoothInputs D)
    (input : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x))
    (hInput : ∀ i, ∃ U : Set (Fin (n+d) → ℝ), IsOpen U ∧
      incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet i ⊆ U ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i) U)
    (hSymm : ∀ p ∈ D.parameterOpen, ∀ x, (input p x).IsSymm)
    (ν : Fin D.primaryCount) (z : P × M)
    (hp : z.1 ∈ D.parameterSet) (hPrimary : z ∈ D.primaryDomain ν) :
    ContinuousAt (fun w : P × M => D.linearArgument ν w.1 w.2 (input w.1 w.2)) z := by
  obtain ⟨a,ha⟩ := D.atlas.cover z.2
  obtain ⟨b,hb,hbn⟩ := hd.parameter_cover z.1 hp
  let i : Fin D.atlas.count × Fin D.parameterCount := (a,b)
  let phi := parameterRound2_originalForwardCoordinates D i
  let W := incrementsOriginalParameterRegion D
  let O := incrementsOriginalDifferentiation D.atlas D.parameterChart i ∩
    (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹' W
  let OL := incrementsOriginalPrimaryDifferentiation D ν i ∩
    (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹' W
  have ha' : z.2 ∈ (D.atlas.chart i.1).source := D.atlas.inner_subset a ha
  have hb' : z.1 ∈ (D.parameterChart i.2).source := hb
  have he := parameterRound2_originalForward_left_inv D i z hb' ha'
  have hm := parameterRound2_originalForward_mem D i z hb' ha'
  have hzW : z ∈ W := ⟨hd.parameter_subset hp,mem_univ _⟩
  have hO : IsOpen O := actual_original_parameter_coordinate_region_open D hd.parameter_open i
  have hOL : IsOpen OL := by
    exact ((actual_original_jointPoint_continuousOn D i).mono inter_subset_left).isOpen_inter_preimage
      (actual_original_primaryDifferentiation_open D hd.primary_open ν i)
      (hd.parameter_open.prod isOpen_univ)
  have hphiO : phi z ∈ O := ⟨hm,by change incrementsOriginalJointPoint _ _ _ _ ∈ W; rw [he]; exact hzW⟩
  have hphiOL : phi z ∈ OL := by
    refine ⟨⟨hm,?_⟩,hphiO.2⟩
    change incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z) ∈ D.primaryDomain ν
    rw [he]
    exact hPrimary
  have hphi : ContinuousAt phi z :=
    (parameterTensorModelEquiv n d).continuous.continuousAt.comp
      ((((D.parameterChart i.2).continuousOn.continuousAt
        ((D.parameterChart i.2).open_source.mem_nhds hb')).comp continuous_fst.continuousAt).prodMk
        (((D.atlas.chart i.1).continuousOn.continuousAt
          ((D.atlas.chart i.1).open_source.mem_nhds ha')).comp continuous_snd.continuousAt))
  have hL := ((hLinear.linear_coordinates ν i).continuousOn.continuousAt
    (hOL.mem_nhds hphiOL)).comp hphi
  obtain ⟨UI,hUI,hSUI,hInputUI⟩ := hInput i
  have hphiS : phi z ∈ incrementsOriginalEvaluation D.atlas D.parameterChart
      D.sourceNormDomain D.parameterNormDomain D.parameterSet i := by
    have hc := parameterRound2_originalForward_components D i z
    have hp' : incrementsOriginalParameterPoint (phi z) = D.parameterChart i.2 z.1 := congrArg Prod.fst hc
    have hx' : incrementsOriginalSourcePoint (phi z) = D.atlas.chart i.1 z.2 := congrArg Prod.snd hc
    refine ⟨hm,?_,?_,?_⟩
    · rw [hx']
      exact hd.source_inner_norm a z.2 ha
    · rw [hp']
      exact hbn
    · change (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z)).1 ∈ D.parameterSet
      rw [he]
      exact hp
  have hA := (hInputUI.continuousOn.continuousAt (hUI.mem_nhds (hSUI hphiS))).comp hphi
  have hreg : ContinuousAt (fun w => actualOriginalCoefficientFunctional n
      (incrementsOriginalLinearArgumentCoordinates D ν i (phi w))
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i (phi w))) z :=
    ((actualOriginalCoefficientFunctional n).continuous.continuousAt.comp hL).clm_apply hA
  apply hreg.congr_of_eventuallyEq
  have hW : IsOpen W := hd.parameter_open.prod isOpen_univ
  filter_upwards [((D.parameterChart i.2).open_source.preimage continuous_fst).mem_nhds hb',
    ((D.atlas.chart i.1).open_source.preimage continuous_snd).mem_nhds ha',hW.mem_nhds hzW] with w hwp hwx hwW
  have hew := parameterRound2_originalForward_left_inv D i w hwp hwx
  have hmw := parameterRound2_originalForward_mem D i w hwp hwx
  have hs : (input (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi w)).1
      (incrementsOriginalJointPoint D.atlas D.parameterChart i (phi w)).2).IsSymm := by
    rw [hew]
    exact hSymm w.1 hwW.1 w.2
  rw [actualOriginalCoefficientFunctional_apply]
  have heq := actual_original_linear_argument_tensor_pairing D hd.atlas_smooth input ν i (phi w) hmw.1 hs
  change incrementsOriginalJointPoint D.atlas D.parameterChart i (phi w) = w at hew
  rw [hew] at heq
  exact heq

#print axioms parameterRound2_original_argument_germ_continuousAt
end GlobalEmbedding.Continuation
