import Repair.ReferenceOriginalLocalFactoryGlobal
import Repair.ReferenceOriginalLocalFactoryBuffer

/-! The actual global plateau around every constructed primary support.
It has compact support in the same genuine normal domain and equals one
on a neighborhood of the entire primary cutoff support. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle Filter
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)
private local instance plateauFactoryProductChart : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance plateauFactoryTargetChart : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
private local instance plateauFactoryProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := 𝓘(ℝ,Ep)) (I' := I) (n := ∞) P M

variable (b : RepairReferenceFactoryBudget m d N)
  (seed : RepairOriginalReferenceSeed (m+1) d N M P)
  (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (fun x => seed.F0 (p,x)))
  (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
  (O K : (Fin seed.atlas.count × Fin seed.parameterCount) →
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))))
  (center : (Fin seed.atlas.count × Fin seed.parameterCount) →
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
  (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF Htensor S i (O i) (K i) (center i))

include hF Htensor O K center in
def repairReferenceOriginalFamilyPlateau
    (nu : Fin (Fintype.card (Σ i, ↥(family i).s × Edge))) : P × M → ℝ :=
  let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
  repairReferenceChartCutoff ((seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1))
    (repairReferencePlateau X b.cutoffRadius a.2.1.val)

include hF Htensor O K center in
theorem repair_reference_original_plateau_target
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (i : Fin seed.atlas.count × Fin seed.parameterCount) (q : (family i).s) (a : Edge) :
    tsupport (repairReferencePlateau X b.cutoffRadius q.val) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).target := by
  intro z hz
  exact repair_reference_original_native_joint_target seed S hSO i z
    (hSample i z (((family i).charts q a).source_domain ((family i).plateau_carrier q a hz).1))

include hF Htensor O K center in
theorem repair_reference_original_family_plateau_properties
    (hseed : RepairReferenceSeedDomains seed)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (nu : Fin (Fintype.card (Σ i, ↥(family i).s × Edge))) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let plateau := repairReferenceOriginalFamilyPlateau b seed hF Htensor S O K center family nu
    IsCompact (tsupport plateau) ∧ ContMDiff IJ 𝓘(ℝ,ℝ) ∞ plateau ∧
      tsupport plateau ⊆ raw.primaryDomain nu ∧
      ∀ z ∈ tsupport (raw.cutoff nu), plateau =ᶠ[𝓝 z] fun _ => 1 := by
  intro raw plateau
  let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
  let q := (seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)
  let eta := repairReferencePlateau X b.cutoffRadius a.2.1.val
  have hCompact : IsCompact (tsupport eta) := by
    rw [repair_reference_plateau_support X b.cutoffRadius b.cutoffRadius_pos a.2.1.val]
    exact isCompact_closedBall _ _
  have hTarget : tsupport eta ⊆ q.target := repair_reference_original_plateau_target
    b seed hF Htensor S O K center family hSO hSample a.1 a.2.1 a.2.2
  have hSupport := repair_reference_chart_cutoff_support q eta hCompact hTarget
  refine ⟨hSupport.1,?_,?_,?_⟩
  · exact repair_reference_chart_cutoff_smooth IJ q eta
      (repair_reference_product_chart_smooth _ (hseed.parameter_charts_smooth a.1.2)
        _ (hseed.atlas_smooth.chart_mem a.1.1))
      (repair_reference_plateau_smooth X b.cutoffRadius a.2.1.val) hCompact hTarget
  · intro z hz
    have hh := hSupport.2 hz
    exact ⟨hh.1,(family a.1).plateau_carrier a.2.1 a.2.2 hh.2⟩
  · intro z hz
    have hInner : z ∈ tsupport (repairReferenceOriginalFamilyInner b seed hF Htensor S O K center family a.1 a.2.1) :=
      tsupport_mul_subset_right hz
    have hOld := (repair_reference_chart_cutoff_support q
      (round4RefinementSquareCutoff X (family a.1).s b.cutoffRadius a.2.1)
      (repair_reference_factory_cutoff_compact b seed hF Htensor S O K center family a.1 a.2.1)
      (repair_reference_factory_cutoff_target b seed hF Htensor S O K center family hSO hSample a.1 a.2.1)).2 hInner
    have hBall : q z ∈ closedBall a.2.1.val (2*b.cutoffRadius) := by
      have hh := tensorLocalNormalizedCutoff_tsupport_subset
        (fun c : (family a.1).s => actualRefinementBump X b.cutoffRadius c.val) a.2.1 hOld.2
      rwa [actualRefinementBump_tsupport X b.cutoffRadius b.cutoffRadius_pos a.2.1.val] at hh
    have hGerm := (repair_reference_plateau_germ X b.cutoffRadius b.cutoffRadius_pos a.2.1.val (q z) hBall).comp_tendsto
      (q.continuousAt hOld.1)
    filter_upwards [q.open_source.mem_nhds hOld.1,hGerm] with y hy hG
    exact (repair_reference_chart_cutoff_on_source q eta hy).trans hG

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_plateau_properties
