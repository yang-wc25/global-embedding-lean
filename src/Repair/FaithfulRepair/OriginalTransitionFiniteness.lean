import FaithfulRepair.OriginalTransitionPrimitives
import FaithfulRepair.OriginalTensorFiniteness
import AuxNormBridge.AllOrderProduct

/-! The existing original parameter/spatial transition budget supplies the
literal source-first joint transition profile.  Consequently the unchanged
original F and H have finite norms at every order on the original Omega/Q/K.
No full input-profile finiteness, chart inverse supplier or tensor-frame
budget is required as an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulRepair

def originalJointTransitionProfile (n d : ℕ) (Parameter Spatial : ℕ → ℝ) (k : ℕ) : ℝ :=
  ‖(parameterTensorModelEquiv n d).toContinuousLinearMap‖ * max (Parameter k) (Spatial k) *
    linearModelFactor (parameterTensorModelEquiv n d).symm k

theorem originalJointTransitionProfile_nonneg (n d : ℕ) (Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ k, 0 ≤ Parameter k) (k : ℕ) :
    0 ≤ originalJointTransitionProfile n d Parameter Spatial k :=
  mul_nonneg (mul_nonneg (norm_nonneg _) ((hParameter k).trans (le_max_left _ _)))
    (linearModelFactor_nonneg _ _)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- A proved source conversion of the existing original geometric budget
to the unchanged joint transition, retaining its actual model factors. -/
theorem repairOriginalTransitionBudgets_joint
    (D : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (Parameter Spatial : ℕ → ℝ) (h : RepairOriginalTransitionBudgets D Parameter Spatial) :
    ∀ p i k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample D (p,i),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition D p i) y‖ ≤
        originalJointTransitionProfile (m+1) d Parameter Spatial k := by
  intro p i k hk y hy
  let a := parameterTensorModelEquiv (m+1) d
  let z := a.symm y
  let ep := (D.parameterChart p.2).symm.trans (D.parameterChart i.2)
  let es := (D.atlas.chart p.1).symm.trans (D.atlas.chart i.1)
  let e := ep.prod es
  have hp : z.1 ∈ ep.source := ⟨hy.2.1.2,hy.2.2.1⟩
  have hs : z.2 ∈ es.source := ⟨hy.2.1.1,hy.2.2.2⟩
  have hps : ContDiffOn ℝ ∞ ep ep.source :=
    (round3Parameter_partial_trans_smooth (D.parameterChart p.2).symm (D.parameterChart i.2)
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.parameter_charts_smooth p.2))
      (contMDiffOn_of_mem_maximalAtlas (hd.parameter_charts_smooth i.2))).contDiffOn
  have hss : ContDiffOn ℝ ∞ es es.source :=
    (round3Parameter_partial_trans_smooth (D.atlas.chart p.1).symm (D.atlas.chart i.1)
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem p.1))
      (contMDiffOn_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1))).contDiffOn
  have he : ContDiffOn ℝ ∞ e e.source := hps.prodMap hss
  have hz : z ∈ e.source := ⟨hp,hs⟩
  have hn : ‖iteratedFDeriv ℝ k e z‖ ≤ max (Parameter k) (Spatial k) :=
    AuxNormBridge.joint_jet_le_partial_product_max ep es z
      (hps.contDiffAt (ep.open_source.mem_nhds hp))
      (hss.contDiffAt (es.open_source.mem_nhds hs)) k (Parameter k) (Spatial k)
      (h.parameter p.2 i.2 k hk z hy.1.2.2.1 ⟨hp,mem_univ _⟩)
      (h.spatial p.1 i.1 k hk z hy.1.2.1 ⟨mem_univ _,hs⟩)
  have hpre := norm_iteratedFDeriv_comp_equiv_le a.symm e k y
  have hsmooth : ContDiffAt ℝ ∞ (e ∘ a.symm) y :=
    (he.contDiffAt (e.open_source.mem_nhds hz)).comp y a.symm.contDiff.contDiffAt
  have hpost := a.toContinuousLinearMap.norm_iteratedFDeriv_comp_left hsmooth (n := k) (by simp)
  change ‖iteratedFDeriv ℝ k (a ∘ e ∘ a.symm) y‖ ≤ _
  apply hpost.trans
  apply (mul_le_mul_of_nonneg_left
    (hpre.trans (mul_le_mul_of_nonneg_right hn (linearModelFactor_nonneg _ _)))
    (norm_nonneg _)).trans_eq
  dsimp only [originalJointTransitionProfile,a]
  ring

/-- The same original map's all-order finiteness from the existing
parameter/spatial primitive, with no additional analytic supplier. -/
theorem original_map_weighted_finite_of_original_geometry
    [R1Space M] [R1Space P] [CompactSpace M]
    (D : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ k, 0 ≤ Parameter k)
    (h : RepairOriginalTransitionBudgets D Parameter Spatial)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet) ≠ ⊤ :=
  original_map_weighted_finite D hd hs (originalJointTransitionProfile (m+1) d Parameter Spatial)
    (originalJointTransitionProfile_nonneg _ _ _ _ hParameter)
    (repairOriginalTransitionBudgets_joint D hd Parameter Spatial h) base j ell

/-- The same native original tensor's all-order finiteness from the
existing primitive, deriving both actual frame factors internally. -/
theorem original_tensor_weighted_finite_of_original_geometry
    [R1Space M] [R1Space P] [CompactSpace M]
    (D : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k)
    (h : RepairOriginalTransitionBudgets D Parameter Spatial)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.H)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet) ≠ ⊤ :=
  original_tensor_weighted_finite D hd hs (originalJointTransitionProfile (m+1) d Parameter Spatial)
    Spatial (originalJointTransitionProfile_nonneg _ _ _ _ hParameter) hSpatial
    (repairOriginalTransitionBudgets_joint D hd Parameter Spatial h)
    (repairOriginalTransitionBudgets_source D hd Parameter Spatial h) base j ell

end GlobalEmbedding.Continuation.FaithfulRepair

#print axioms GlobalEmbedding.Continuation.FaithfulRepair.repairOriginalTransitionBudgets_joint
#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_map_weighted_finite_of_original_geometry
#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_tensor_weighted_finite_of_original_geometry
