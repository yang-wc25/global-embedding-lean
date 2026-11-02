import Repair.EndpointFactoryLinearInputs
import Repair.EndpointOriginalPrimaryRegularity
import Repair.IncrementCutoffObserverJets

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance globalFactoryRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance globalFactorySquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

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
private local instance globalFactoryProductChart : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance globalFactoryTargetChart : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
private local instance globalFactoryProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
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


theorem repairReferenceFactoryCutoffProfile_nonneg (b : RepairReferenceFactoryBudget m d N) (j : ℕ) :
    0 ≤ b.cutoffProfile j := by
  apply round4RefinementSquareProfile_nonneg
  exact b.cutoffRadius_pos

def repairReferenceCutoffNativeProfile (b : RepairReferenceFactoryBudget m d N)
    (Parent T : ℕ → ℝ) (j : ℕ) : ℝ :=
  tensorProductJetConstant Parent (repairEntranceCompositionProfile b.cutoffProfile T) j

def repairReferenceCutoffOriginalProfile (b : RepairReferenceFactoryBudget m d N)
    (Parent T : ℕ → ℝ) (j : ℕ) : ℝ :=
  ‖repairScalarOutput‖*repairReferenceCutoffNativeProfile b Parent T j*
    ‖(parameterTensorModelEquiv (m+1) d).symm.toContinuousLinearMap‖^j

theorem repairReferenceCutoffOriginalProfile_nonneg
    (b : RepairReferenceFactoryBudget m d N) (Parent T : ℕ → ℝ)
    (hParent : ∀ j, 0 ≤ Parent j) (hT : ∀ j, 0 ≤ T j) (j : ℕ) :
    0 ≤ repairReferenceCutoffOriginalProfile b Parent T j := by
  have hC := repairEntranceCompositionProfile_nonneg b.cutoffProfile T
    (repairReferenceFactoryCutoffProfile_nonneg b) hT
  have h := tensorProductJetConstant_nonneg hParent hC j
  unfold repairReferenceCutoffOriginalProfile repairReferenceCutoffNativeProfile
  positivity

include hF Htensor O K center in
/-- The actual global cutoff is exactly the original parent times the local
square-normalized refinement. Its all-order original norm uses only the
actual original parent and transition derivatives. -/
theorem repair_reference_original_family_cutoff_jets
    (hseed : RepairReferenceSeedDomains seed)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (hOuter : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (outer i))
    (hSupport : ∀ i, tsupport (outer i) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).source)
    (Parent T : ℕ → ℝ) (hParent : ∀ j, 0 ≤ Parent j) (hT : ∀ j, 0 ≤ T j)
    (nu : Fin (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).primaryCount)
    (i : Fin seed.atlas.count × Fin seed.parameterCount)
    (y : Fin (m+1+d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hParentJets : ∀ k,
      let ix := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      let observer := (seed.parameterChart i.2).prod (seed.atlas.chart i.1)
      ‖iteratedFDeriv ℝ k (outer ix.1 ∘ observer.symm)
        ((parameterTensorModelEquiv (m+1) d).symm y)‖ ≤ Parent k)
    (hTransition : ∀ k, 1 ≤ k →
      let ix := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      let owner := (seed.parameterChart ix.1.2).prod (seed.atlas.chart ix.1.1)
      let observer := (seed.parameterChart i.2).prod (seed.atlas.chart i.1)
      observer.symm ((parameterTensorModelEquiv (m+1) d).symm y) ∈ tsupport (outer ix.1) →
      ‖iteratedFDeriv ℝ k (owner ∘ observer.symm)
        ((parameterTensorModelEquiv (m+1) d).symm y)‖ ≤ T k)
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j (incrementsOriginalScalarCoordinates
      (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer)
      ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).cutoff nu) i) y‖ ≤
        repairReferenceCutoffOriginalProfile b Parent T j := by
  let data := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
  let ix := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
  let owner := (seed.parameterChart ix.1.2).prod (seed.atlas.chart ix.1.1)
  let observer := (seed.parameterChart i.2).prod (seed.atlas.chart i.1)
  let phi := round4RefinementSquareCutoff X (family ix.1).s b.cutoffRadius ix.2.1
  let a := parameterTensorModelEquiv (m+1) d
  have ho : owner ∈ IsManifold.maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hseed.parameter_charts_smooth ix.1.2)
      (hseed.atlas_smooth.chart_mem ix.1.1)
  have he : observer ∈ IsManifold.maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hseed.parameter_charts_smooth i.2)
      (hseed.atlas_smooth.chart_mem i.1)
  have hLiteral : data.cutoff nu = fun z => outer ix.1 z*phi (owner z) := by
    funext z
    change outer ix.1 z*repairReferenceChartCutoff owner phi z = _
    by_cases hz : z ∈ owner.source
    · rw [repair_reference_chart_cutoff_on_source owner phi hz]
    · have hz0 : outer ix.1 z = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hz (hSupport ix.1 hh))
      simp only [hz0,zero_mul]
  have hParentSmooth := hOuter ix.1
  rw [← modelWithCornersSelf_prod] at hParentSmooth
  have hz : a.symm y ∈ observer.target := ⟨hy.2,hy.1⟩
  have hj := increment_physical_refinement_observer_jets owner observer ho he
    (outer ix.1) (data.cutoff nu) phi hParentSmooth ((family ix.1).cutoff_smooth ix.2.1)
    (hSupport ix.1) hLiteral Parent b.cutoffProfile T hParent
    (repairReferenceFactoryCutoffProfile_nonneg b) hT
    ((family ix.1).cutoff_jets ix.2.1) (a.symm y) hz hParentJets
    (fun hh k hk => hTransition k hk hh) j
  have hInner := repair_reference_chart_cutoff_smooth IJ owner phi
    (repair_reference_product_chart_smooth _ (hseed.parameter_charts_smooth ix.1.2)
      _ (hseed.atlas_smooth.chart_mem ix.1.1)) ((family ix.1).cutoff_smooth ix.2.1)
    (repair_reference_factory_cutoff_compact b seed hF Htensor S O K center family ix.1 ix.2.1)
    (repair_reference_factory_cutoff_target b seed hF Htensor S O K center family hSO hSample ix.1 ix.2.1)
  have hCut : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,ℝ) ∞ (data.cutoff nu) := by
    rw [modelWithCornersSelf_prod]
    exact (hOuter ix.1).mul hInner
  have hs : ContDiffOn ℝ ∞ (data.cutoff nu ∘ observer.symm) observer.target :=
    (hCut.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn
  exact repair_original_output_coordinate_jet a repairScalarOutput (data.cutoff nu ∘ observer.symm)
    observer.target observer.open_target hs y hz j _ hj

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_cutoff_jets
