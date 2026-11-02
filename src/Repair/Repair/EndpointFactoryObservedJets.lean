import Repair.EndpointFactoryNormalJets
import Repair.EndpointFactoryCutoffJets
import Repair.EndpointFactoryLinearJets
import Repair.EndpointSpatialTransitionJets
import Probes.ActualIncrementOriginalSampling

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


include hF Htensor O K center in
/-- All three remaining original fixed-packet fields are estimated from
original sampling, original transition derivatives and the actual factory.
The reverse transition used by the linear coefficient field is evaluated
in the genuine owner sampling set supplied by the same normal carrier. -/
theorem repair_reference_original_factory_observed_jets
    (hseed : RepairReferenceSeedDomains seed)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (hSEval : ∀ i, S i ⊆ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (hOuter : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (outer i))
    (hSupport : ∀ i, tsupport (outer i) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).source)
    (R Parent Parameter Spatial : ℕ → ℝ)
    (hR : ∀ j, 0 ≤ R j) (hParent : ∀ j, 0 ≤ Parent j)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (hMap : ∀ j, paperAtlasCj (j+2)
      (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S ≤ ENNReal.ofReal (R (j+2)))
    (Bs : ℝ) (hBs : 0 ≤ Bs)
    (hRadius : ∀ i x, x ∈ seed.sourceNormDomain i → ‖x‖ ≤ Bs)
    (hParentJets : ∀ owner i k y, y ∈ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i →
      ‖iteratedFDeriv ℝ k (outer owner ∘ ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).symm)
        ((parameterTensorModelEquiv (m+1) d).symm y)‖ ≤ Parent k) :
    let data := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let Joint := fun k => max (Parameter k) (Spatial k)
    let Source := repairOriginalSpatialFullProfile Bs Spatial
    ∀ (hd : IncrementsOriginalDomainConditions data)
      (transition : RepairOriginalTransitionBudgets data Parameter Spatial)
      (nu : Fin data.primaryCount) (i : Fin seed.atlas.count × Fin seed.parameterCount) k y, y ∈ incrementsOriginalPrimaryEvaluation data nu i →
    ‖iteratedFDeriv ℝ k (incrementsOriginalScalarCoordinates data (data.cutoff nu) i) y‖ ≤
      repairReferenceCutoffOriginalProfile b Parent Joint k ∧
    ‖iteratedFDeriv ℝ k (incrementsOriginalMapCoordinates data.atlas data.parameterChart (data.freeNormal nu) i) y‖ ≤
      repairReferenceNormalOriginalProfile b R Joint k ∧
    ‖iteratedFDeriv ℝ k (incrementsOriginalLinearArgumentCoordinates data nu i) y‖ ≤
      repairOriginalJointLinearProfile (m+1) d b.cover.coefficientBound Source k := by
  intro data Joint Source hd transition nu i k y hy
  let ix := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
  let z := incrementsOriginalJointPoint seed.atlas seed.parameterChart i y
  let owner := (seed.parameterChart ix.1.2).prod (seed.atlas.chart ix.1.1)
  have hPrimary : y ∈ incrementsOriginalPrimaryDifferentiation data nu i := ⟨hy.1.1,hy.2⟩
  have hJoint : ∀ l, 0 ≤ Joint l := fun l => (hParameter l).trans (le_max_left _ _)
  have hSource : ∀ l, 0 ≤ Source l := repairOriginalSpatialFullProfile_nonneg Bs Spatial hBs hSpatial
  have hOwn : z ∈ owner.source := hy.2.1
  have hJointAt : ∀ l, 1 ≤ l →
      ‖iteratedFDeriv ℝ l (owner ∘ ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).symm)
        ((parameterTensorModelEquiv (m+1) d).symm y)‖ ≤ Joint l := by
    intro l hl
    exact (increment_given_actual_native_transition_jets data hd Parameter Spatial transition
      (i,ix.1) y ⟨hy.1,⟨hy.1.1,hOwn⟩⟩ l hl).2
  have hC := repair_reference_original_family_cutoff_jets b seed hF Htensor S O K center family
    hseed hSO hSample outer hOuter hSupport Parent Joint hParent hJoint nu i y hy.1.1
    (hParentJets ix.1 i · y hy.1) (by
      intro l hl
      dsimp only
      intro hActive
      exact (increment_given_actual_native_transition_jets data hd Parameter Spatial transition
        (i,ix.1) y ⟨hy.1,⟨hy.1.1,hSupport ix.1 hActive⟩⟩ l hl).2) k
  have hN := repair_reference_original_family_normal_jets b seed hF Htensor S O K center family
    hseed outer R Joint hR hJoint hMap nu i y hPrimary hJointAt k
  refine ⟨hC,hN,?_⟩
  apply repair_reference_original_family_linear_jets b seed hF Htensor S O K center family
    hseed outer Source hSource nu i y hPrimary _ _ k
  · intro l hl
    have hb := repair_original_spatial_transition_jets data hd Parameter Spatial transition i.1 ix.1.1
      (incrementsOriginalSourcePoint y) hy.1.2.1 ⟨hy.1.1.1,hOwn.2⟩ l hl
    calc
      _ ≤ Spatial l := hb
      _ = Source l := by simp only [Source,repairOriginalSpatialFullProfile,ite_eq_right (show l ≠ 0 by omega)]
  · intro l
    have hOwnerSample := hSEval ix.1 (hSample ix.1 (owner z)
      (((family ix.1).charts ix.2.1 ix.2.2).source_domain hy.2.2.1))
    have hOwnerNorm : seed.atlas.chart ix.1.1 z.2 ∈ seed.sourceNormDomain ix.1.1 :=
      ((actual_original_native_evaluation_iff data hd ix.1 (owner z)).mp hOwnerSample).1
    have hBack : seed.atlas.chart ix.1.1 z.2 ∈
        ((seed.atlas.chart ix.1.1).symm.trans (seed.atlas.chart i.1)).source := by
      refine ⟨(seed.atlas.chart ix.1.1).map_source hOwn.2,?_⟩
      change (seed.atlas.chart ix.1.1).symm (seed.atlas.chart ix.1.1 z.2) ∈ (seed.atlas.chart i.1).source
      rw [(seed.atlas.chart ix.1.1).left_inv hOwn.2]
      exact (seed.atlas.chart i.1).map_target hy.1.1.1
    by_cases hl : l=0
    · subst l
      simp only [Source,repairOriginalSpatialFullProfile,ite_true,norm_iteratedFDeriv_zero,Function.comp_apply]
      change ‖seed.atlas.chart i.1 ((seed.atlas.chart ix.1.1).symm (seed.atlas.chart ix.1.1 z.2))‖ ≤ Bs
      rw [(seed.atlas.chart ix.1.1).left_inv hOwn.2]
      change ‖seed.atlas.chart i.1 ((seed.atlas.chart i.1).symm (incrementsOriginalSourcePoint y))‖ ≤ Bs
      rw [(seed.atlas.chart i.1).right_inv hy.1.1.1]
      exact hRadius i.1 _ hy.1.2.1
    · have hb := repair_original_spatial_transition_jets data hd Parameter Spatial transition ix.1.1 i.1
        (seed.atlas.chart ix.1.1 z.2) hOwnerNorm hBack l (by omega)
      calc
        _ ≤ Spatial l := hb
        _ = Source l := by simp only [Source,repairOriginalSpatialFullProfile,ite_eq_right hl]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_original_factory_observed_jets
