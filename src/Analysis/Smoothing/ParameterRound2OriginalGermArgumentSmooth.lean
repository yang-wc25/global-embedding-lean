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

/-- Local smoothness of the original native argument follows from an actual
original coordinate germ, the unchanged original L coordinates, and the true
joint forward chart. No joint native regularity premise is added. -/
theorem parameterRound2_original_argument_contMDiffAt_of_coordinate_germ
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hLinear : IncrementsOriginalLinearSmoothInputs D)
    (input : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x))
    (hSymm : ∀ p ∈ D.parameterOpen, ∀ x, (input p x).IsSymm)
    (i : Fin D.atlas.count × Fin D.parameterCount)
    (UI : Set (Fin (n+d) → ℝ)) (hUI : IsOpen UI)
    (hInputUI : ContDiffOn ℝ ∞
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i) UI)
    (ν : Fin D.primaryCount) (z : P × M)
    (hp : z.1 ∈ (D.parameterChart i.2).source) (hx : z.2 ∈ (D.atlas.chart i.1).source)
    (hzW : z ∈ incrementsOriginalParameterRegion D) (hPrimary : z ∈ D.primaryDomain ν)
    (hzUI : parameterRound2_originalForwardCoordinates D i z ∈ UI) :
    ContMDiffAt ((𝓘(ℝ,EuclideanSpace ℝ (Fin d))).prod (𝓘(ℝ,EuclideanSpace ℝ (Fin n))))
      𝓘(ℝ,ℝ) ∞ (fun w : P × M => D.linearArgument ν w.1 w.2 (input w.1 w.2)) z := by
  let phi := parameterRound2_originalForwardCoordinates D i
  let W := incrementsOriginalParameterRegion D
  let OL := incrementsOriginalPrimaryDifferentiation D ν i ∩
    (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹' W
  have he := parameterRound2_originalForward_left_inv D i z hp hx
  have hm := parameterRound2_originalForward_mem D i z hp hx
  have hOL : IsOpen OL :=
    ((actual_original_jointPoint_continuousOn D i).mono inter_subset_left).isOpen_inter_preimage
      (actual_original_primaryDifferentiation_open D hd.primary_open ν i)
      (hd.parameter_open.prod isOpen_univ)
  have hphiOL : phi z ∈ OL := by
    refine ⟨⟨hm,?_⟩,?_⟩
    · change incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z) ∈ D.primaryDomain ν
      rw [he]
      exact hPrimary
    · change incrementsOriginalJointPoint D.atlas D.parameterChart i (phi z) ∈ W
      rw [he]
      exact hzW
  have hphi : ContMDiffAt
      ((𝓘(ℝ,EuclideanSpace ℝ (Fin d))).prod (𝓘(ℝ,EuclideanSpace ℝ (Fin n))))
      𝓘(ℝ,Fin (n+d) → ℝ) ∞ phi z :=
    (parameterTensorModelEquiv n d).contDiff.comp_contMDiffAt
      ((((contMDiffOn_of_mem_maximalAtlas (hd.parameter_charts_smooth i.2)).contMDiffAt
        ((D.parameterChart i.2).open_source.mem_nhds hp)).comp z contMDiffAt_fst).prodMk_space
        (((contMDiffOn_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1)).contMDiffAt
          ((D.atlas.chart i.1).open_source.mem_nhds hx)).comp z contMDiffAt_snd))
  have hL := ((hLinear.linear_coordinates ν i).contDiffAt
    (hOL.mem_nhds hphiOL)).comp_contMDiffAt hphi
  have hA := (hInputUI.contDiffAt (hUI.mem_nhds hzUI)).comp_contMDiffAt hphi
  have hreg : ContMDiffAt
      ((𝓘(ℝ,EuclideanSpace ℝ (Fin d))).prod (𝓘(ℝ,EuclideanSpace ℝ (Fin n))))
      𝓘(ℝ,ℝ) ∞ (fun w => actualOriginalCoefficientFunctional n
        (incrementsOriginalLinearArgumentCoordinates D ν i (phi w))
        (incrementsOriginalTensorCoordinates D.atlas D.parameterChart input i (phi w))) z :=
    ((actualOriginalCoefficientFunctional n).contDiff.comp_contMDiffAt hL).clm_apply hA
  apply hreg.congr_of_eventuallyEq
  have hW : IsOpen W := hd.parameter_open.prod isOpen_univ
  filter_upwards [((D.parameterChart i.2).open_source.preimage continuous_fst).mem_nhds hp,
    ((D.atlas.chart i.1).open_source.preimage continuous_snd).mem_nhds hx,hW.mem_nhds hzW] with w hwp hwx hwW
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

#print axioms parameterRound2_original_argument_contMDiffAt_of_coordinate_germ
end GlobalEmbedding.Continuation
