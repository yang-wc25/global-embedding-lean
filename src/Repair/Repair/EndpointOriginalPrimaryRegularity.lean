import Repair.EndpointObserverCoordinateJets
import Probes.ActualOriginalInputJets

/-! Coordinate regularity on the original primary domains, including all
parameter variables. On a compact parameter manifold parameterOpen is
univ; no boundary or closed-initial-state assumption is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
private local instance primaryRegProductChart : ChartedSpace X (P × M) := prodChartedSpace Ep P D M
private local instance primaryRegTargetChart : ChartedSpace X X := chartedSpaceSelf X
private local instance primaryRegProductManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem repair_original_coordinate_field_smooth
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (field : P × M → F) (U : Set (P × M))
    (hField : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,F) ∞ field U)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    ContDiffOn ℝ ∞ (field ∘ incrementsOriginalJointPoint Data.atlas Data.parameterChart i)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart i ∩
        (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) ⁻¹' U) := by
  let e := (Data.parameterChart i.2).prod (Data.atlas.chart i.1)
  let a := parameterTensorModelEquiv n d
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hd.parameter_charts_smooth i.2) (hd.atlas_smooth.chart_mem i.1)
  have hNative : ContDiffOn ℝ ∞ (field ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) :=
    (hField.comp ((contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left)
      (fun _ hy => hy.2)).contDiffOn
  exact hNative.comp a.symm.contDiff.contDiffOn (fun _ hy => ⟨⟨hy.1.2,hy.1.1⟩,hy.2⟩)

theorem repair_original_primary_normal_smooth
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hOpen : Data.parameterOpen = univ) (nu : Fin Data.primaryCount)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal nu) i)
      (incrementsOriginalPrimaryDifferentiation Data nu i) := by
  have hn := hs.normal_joint nu
  rw [← modelWithCornersSelf_prod] at hn
  have hN : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ (Data.freeNormal nu) (Data.primaryDomain nu) := by
    simpa only [incrementsOriginalParameterRegion,hOpen,univ_prod_univ,inter_univ] using hn
  exact (EuclideanSpace.equiv (Fin N) ℝ).contDiff.comp_contDiffOn
    (repair_original_coordinate_field_smooth Data hd _ _ hN i)

def repairScalarOutput : ℝ →L[ℝ] (Fin 1 → ℝ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ

theorem repair_original_primary_cutoff_smooth
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hOpen : Data.parameterOpen = univ) (nu : Fin Data.primaryCount)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    ContDiffOn ℝ ∞ (incrementsOriginalScalarCoordinates Data (Data.cutoff nu) i)
      (incrementsOriginalPrimaryDifferentiation Data nu i) := by
  have hc := hs.cutoff_joint nu
  rw [← modelWithCornersSelf_prod] at hc
  have hC : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,ℝ) ∞ (Data.cutoff nu) (Data.primaryDomain nu) := by
    simpa only [incrementsOriginalParameterRegion,hOpen,univ_prod_univ,inter_univ] using hc
  exact repairScalarOutput.contDiff.comp_contDiffOn
    (repair_original_coordinate_field_smooth Data hd _ _ hC i)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_original_primary_normal_smooth
#print axioms GlobalEmbedding.Continuation.repair_original_primary_cutoff_smooth
