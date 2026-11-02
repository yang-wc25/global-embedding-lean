import Repair.ReferenceOriginalLocalFactoryPlateau
import Repair.EndpointCutoffObserverJets
import Smoothing.TensorTransferJets

/-! Uniform observer jets of the same genuine primary plateaus, followed
by the actual parent-times-plateau cutoff. Only the fixed model bump and
the original parent/transition derivative profiles are read. -/

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


def repairReferenceFactoryPlateauProfile (b : RepairReferenceFactoryBudget m d N) (j : ℕ) : ℝ :=
  repairReferencePlateauJetCost (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))) j/b.cutoffRadius^j

theorem repairReferenceFactoryPlateauProfile_nonneg (b : RepairReferenceFactoryBudget m d N) (j : ℕ) :
    0 ≤ repairReferenceFactoryPlateauProfile b j :=
  div_nonneg (repair_reference_plateau_jet_cost_nonneg _ _) (pow_pos b.cutoffRadius_pos j).le

include hF Htensor O K center in
theorem repair_reference_original_family_plateau_observer_jets
    (hseed : RepairReferenceSeedDomains seed)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (nu : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)))
    (i : Fin seed.atlas.count × Fin seed.parameterCount)
    (z : X) (hz : z ∈ ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).target)
    (hTransition : ∀ j, 1 ≤ j →
      let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      let owner := (seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)
      let observer := (seed.parameterChart i.2).prod (seed.atlas.chart i.1)
      observer.symm z ∈ owner.source → ‖iteratedFDeriv ℝ j (owner ∘ observer.symm) z‖ ≤ T j)
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j (repairReferenceOriginalFamilyPlateau b seed hF Htensor S O K center family nu ∘
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).symm) z‖ ≤
      repairEntranceCompositionProfile (repairReferenceFactoryPlateauProfile b) T j := by
  let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
  let owner := (seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)
  let observer := (seed.parameterChart i.2).prod (seed.atlas.chart i.1)
  have ho : owner ∈ IsManifold.maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hseed.parameter_charts_smooth a.1.2)
      (hseed.atlas_smooth.chart_mem a.1.1)
  have he : observer ∈ IsManifold.maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hseed.parameter_charts_smooth i.2)
      (hseed.atlas_smooth.chart_mem i.1)
  apply repair_zero_extended_cutoff_observer_jets owner observer ho he
    (repairReferencePlateau X b.cutoffRadius a.2.1.val)
    (repair_reference_plateau_smooth X b.cutoffRadius a.2.1.val)
    (by rw [repair_reference_plateau_support X b.cutoffRadius b.cutoffRadius_pos a.2.1.val]
        exact isCompact_closedBall _ _)
    (repair_reference_original_plateau_target b seed hF Htensor S O K center family hSO hSample a.1 a.2.1 a.2.2)
    (repairReferenceFactoryPlateauProfile b) T (repairReferenceFactoryPlateauProfile_nonneg b) hT
    _ z hz (fun h j hj => hTransition j hj h) j
  intro k y
  apply (le_div_iff₀ (pow_pos b.cutoffRadius_pos k)).mpr
  simpa only [mul_comm] using repair_reference_plateau_weighted_jets X b.cutoffRadius
    b.cutoffRadius_pos a.2.1.val y k

include hF Htensor O K center in
theorem repair_reference_original_family_primary_cutoff_observer_jets
    (hseed : RepairReferenceSeedDomains seed)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (theta : P × M → ℝ) (hTheta : ContMDiff IJ 𝓘(ℝ,ℝ) ∞ theta)
    (Parent T : ℕ → ℝ) (hParent : ∀ j, 0 ≤ Parent j) (hT : ∀ j, 0 ≤ T j)
    (nu : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)))
    (i : Fin seed.atlas.count × Fin seed.parameterCount)
    (z : X) (hz : z ∈ ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).target)
    (hParentJets : ∀ j, ‖iteratedFDeriv ℝ j
      (theta ∘ ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).symm) z‖ ≤ Parent j)
    (hTransition : ∀ j, 1 ≤ j →
      let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      let owner := (seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)
      let observer := (seed.parameterChart i.2).prod (seed.atlas.chart i.1)
      observer.symm z ∈ owner.source → ‖iteratedFDeriv ℝ j (owner ∘ observer.symm) z‖ ≤ T j)
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j ((fun y => theta y *
      repairReferenceOriginalFamilyPlateau b seed hF Htensor S O K center family nu y) ∘
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).symm) z‖ ≤
      tensorProductJetConstant Parent
        (repairEntranceCompositionProfile (repairReferenceFactoryPlateauProfile b) T) j := by
  let observer := (seed.parameterChart i.2).prod (seed.atlas.chart i.1)
  let plateau := repairReferenceOriginalFamilyPlateau b seed hF Htensor S O K center family nu
  have he : observer ∈ IsManifold.maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hseed.parameter_charts_smooth i.2)
      (hseed.atlas_smooth.chart_mem i.1)
  have hp := (repair_reference_original_family_plateau_properties b seed hF Htensor S O K center family
    hseed hSO hSample (fun _ _ => 0) nu).2.1
  have hTheta' : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,ℝ) ∞ theta := by
    rw [modelWithCornersSelf_prod]
    exact hTheta
  have hp' : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,ℝ) ∞ plateau := by
    rw [modelWithCornersSelf_prod]
    exact hp
  have hThetaSmooth : ContDiffOn ℝ ∞ (theta ∘ observer.symm) observer.target :=
    (hTheta'.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn
  have hPlateauSmooth : ContDiffOn ℝ ∞ (plateau ∘ observer.symm) observer.target :=
    (hp'.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn
  exact tensor_scalar_product_jet_le Parent
    (repairEntranceCompositionProfile (repairReferenceFactoryPlateauProfile b) T) hParent
    (repairEntranceCompositionProfile_nonneg _ _ (repairReferenceFactoryPlateauProfile_nonneg b) hT)
    observer.open_target hThetaSmooth hPlateauSmooth hz j hParentJets
    (repair_reference_original_family_plateau_observer_jets b seed hF Htensor S O K center family
      hseed hSO hSample T hT nu i z hz hTransition)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_plateau_observer_jets
#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_primary_cutoff_observer_jets
