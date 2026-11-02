import Probes.ActualOriginalInputJets
import Probes.ActualIncrementOriginalCoordinateJets

/-! The unchanged original Core controls the SAME native map on its actual
parameter-open neighborhood. The differentiation region is restricted only
by a proved locality equality of the original weighted norm. No full-parameter
smoothness, boundary extension or additional coordinate budget is assumed. -/

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
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es

private local instance openCoreProductCharted : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance openCoreProductManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

theorem actual_original_map_coordinates_parameter_open
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F i)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart i ∩
        (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
          incrementsOriginalParameterRegion D) := by
  let e := (D.parameterChart i.2).prod (D.atlas.chart i.1)
  let a := parameterTensorModelEquiv n d
  let cy := EuclideanSpace.equiv (Fin N) ℝ
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hd.parameter_charts_smooth i.2)
      (hd.atlas_smooth.chart_mem i.1)
  have hF : ContMDiffOn 𝓘(ℝ,Ep × Es) 𝓘(ℝ,V) ∞ D.F (incrementsOriginalParameterRegion D) := by
    rw [modelWithCornersSelf_prod]
    exact hs.F_joint
  have hup : ContMDiffOn 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Fin N → ℝ) ∞ (cy ∘ D.F)
      (incrementsOriginalParameterRegion D) := cy.contDiff.contMDiff.comp_contMDiffOn hF
  letI : ChartedSpace (Ep × Es) (Ep × Es) := chartedSpaceSelf (Ep × Es)
  have hi : ContMDiffOn 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ep × Es) ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas he
  have hnative : ContDiffOn ℝ ∞ ((cy ∘ D.F) ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' incrementsOriginalParameterRegion D) :=
    (hup.comp (hi.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  have hmap : MapsTo a.symm
      (incrementsOriginalDifferentiation D.atlas D.parameterChart i ∩
        (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
          incrementsOriginalParameterRegion D)
      (e.target ∩ e.symm ⁻¹' incrementsOriginalParameterRegion D) := by
    intro y hy
    exact ⟨⟨hy.1.2,hy.1.1⟩,hy.2⟩
  exact hnative.comp a.symm.contDiff.contDiffOn hmap

/-- The real native open product-chart domain; the compact sampling set is
still precisely the original evaluation domain. -/
def actualOriginalNativeOpen
    (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount) : Set X :=
  (parameterTensorModelEquiv n d) ⁻¹'
    (incrementsOriginalDifferentiation D.atlas D.parameterChart i ∩
      (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
        incrementsOriginalParameterRegion D)

theorem actualOriginalNativeOpen_isOpen
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (i : Fin D.atlas.count × Fin D.parameterCount) : IsOpen (actualOriginalNativeOpen D i) :=
  (actual_original_parameter_coordinate_region_open D hd.parameter_open i).preimage
    (parameterTensorModelEquiv n d).continuous

theorem actualOriginalNativeOpen_parameter
    (D : IncrementsOriginalNativeData n d N M P)
    (i : Fin D.atlas.count × Fin D.parameterCount)
    {z : X} (hz : z ∈ actualOriginalNativeOpen D i) :
    (D.parameterChart i.2).symm z.1 ∈ D.parameterOpen := by
  have hp := congrArg Prod.fst ((parameterTensorModelEquiv n d).symm_apply_apply z)
  change incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z) = z.1 at hp
  have hh := hz.2.1
  change (D.parameterChart i.2).symm
    (incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z)) ∈ D.parameterOpen at hh
  rwa [hp] at hh

theorem actualOriginalNativeOpen_evaluation_subset
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    (parameterTensorModelEquiv n d) ⁻¹'
      incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet i ⊆ actualOriginalNativeOpen D i := by
  intro z hz
  exact ⟨hz.1,hd.parameter_subset hz.2.2.2,mem_univ _⟩

theorem actualOriginalNativeMap_contDiffOn_parameter_open
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    ContDiffOn ℝ ∞ (actualOriginalNativeMap D i) (actualOriginalNativeOpen D i) := by
  rw [actualOriginalNativeMap_eq_coordinate]
  exact (EuclideanSpace.equiv (Fin N) ℝ).symm.contDiff.comp_contDiffOn
    ((actual_original_map_coordinates_parameter_open D hd hs i).comp
      (parameterTensorModelEquiv n d).contDiff.contDiffOn (fun _ hx => hx))

theorem actual_original_parameter_open_core_shifted_jets
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hfinite : incrementsOriginalCoreInputProfile D j ell ≠ ⊤)
    (i : Fin D.atlas.count × Fin D.parameterCount)
    {k b : ℕ} (hk : k ≤ j) (hb : b ≤ 2)
    {z : X} (hz : parameterTensorModelEquiv n d z ∈
      incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet i) :
    ell^k*‖iteratedFDeriv ℝ (k+b) (actualOriginalNativeMap D i) z‖ ≤
      actualOriginalMapJetCost n d N j*(incrementsOriginalCoreInputProfile D j ell).toReal := by
  let O := incrementsOriginalDifferentiation D.atlas D.parameterChart
  let U := fun i => O i ∩ (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
    incrementsOriginalParameterRegion D
  let S := incrementsOriginalEvaluation D.atlas D.parameterChart
    D.sourceNormDomain D.parameterNormDomain D.parameterSet
  let f := incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open D.atlas D.parameterChart
  have hU : ∀ i, IsOpen (U i) := actual_original_parameter_coordinate_region_open D hd.parameter_open
  have hSU : ∀ i, S i ⊆ U i := by
    intro i y hy
    exact ⟨hy.1,hd.parameter_subset hy.2.2.2,mem_univ _⟩
  have he := actual_paperAtlasWeighted_open_restrict 2 j ell f O U S hO hU
    (fun _ => inter_subset_left) hSU
  have hle := parameterOriginalCore_map_le D j ell
  have hfinit : paperAtlasWeighted 2 j ell f U S ≠ ⊤ :=
    he ▸ ne_top_of_le_ne_top hfinite hle
  rw [actualOriginalNativeMap_eq_coordinate]
  have hh := paperAtlasWeighted_native_shifted_joint_jet_le
    (parameterTensorModelEquiv n d) (EuclideanSpace.equiv (Fin N) ℝ).symm
    2 j ell hell f U S hU hSU (actual_original_map_coordinates_parameter_open D hd hs)
    hfinit i hk hb hz
  rw [← he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfinite hle)
    (actualOriginalMapJetCost_nonneg n d N j))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_map_coordinates_parameter_open
#print axioms GlobalEmbedding.Continuation.actual_original_parameter_open_core_shifted_jets
