import Repair.EndpointActualFixedBudget
import Smoothing.ParameterRound2CompactNorms

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



def repairReferenceCompletedMapProfile
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (J : ℕ) (R : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j ≤ J+2 then R j else
    (paperAtlasCj j (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S).toReal

theorem repairReferenceCompletedMapProfile_nonneg
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (J : ℕ) (R : ℕ → ℝ) (hR : ∀ j, 0 ≤ R j) (j : ℕ) :
    0 ≤ repairReferenceCompletedMapProfile seed S J R j := by
  unfold repairReferenceCompletedMapProfile
  split_ifs
  · exact hR j
  · exact ENNReal.toReal_nonneg

theorem repair_reference_completed_map_bound
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hseed : RepairReferenceSeedDomains seed)
    (hFjoint : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ seed.F0)
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hCompact : ∀ i, IsCompact (S i)) (J : ℕ) (R : ℕ → ℝ)
    (hMap : ∀ j, j ≤ J+2 → (paperAtlasCj j
      (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S).toReal ≤ R j)
    (j : ℕ) :
    paperAtlasCj j (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S ≤
        ENNReal.ofReal (repairReferenceCompletedMapProfile seed S J R j) := by
  have hf := parameterRound2_originalMapCoordinates_contDiffOn seed.atlas seed.parameterChart
    hseed.atlas_smooth hseed.parameter_charts_smooth seed.F0 hFjoint
  have hFinite := parameterRound2_paperAtlasCj_finite_of_compact _ _ S
    (parameterRound2_originalDifferentiation_open seed.atlas seed.parameterChart) hCompact hSO hf j
  apply repair_ennreal_le_of_actual_bound hFinite
  unfold repairReferenceCompletedMapProfile
  split_ifs with hj
  · exact hMap j hj
  · exact le_rfl

include hF Htensor O K center in
/-- The actual complete fixed packet has a uniform finite reference prefix.
Only F0 derivatives through J+2 obey prescribed bounds; every higher
derivative is taken from the particular smooth map on compact original
samples. This construction supplies finiteness at all higher orders. -/
theorem repair_reference_actual_factory_finite_fixed_budget
    (hseed : RepairReferenceSeedDomains seed)
    (hFjoint : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ seed.F0)
    (hOpen : seed.parameterOpen=univ)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (hSEval : ∀ i, S i ⊆ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (hOuter : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (outer i))
    (hSupport : ∀ i, tsupport (outer i) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).source)
    (J : ℕ) (R Parent Parameter Spatial : ℕ → ℝ)
    (hR : ∀ j, 0 ≤ R j) (hParent : ∀ j, 0 ≤ Parent j)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (hCompact : ∀ i, IsCompact (S i))
    (hMap : ∀ j, j ≤ J+2 → (paperAtlasCj j
      (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S).toReal ≤ R j)
    (Bs : ℝ) (hBs : 0 ≤ Bs)
    (hRadius : ∀ i x, x ∈ seed.sourceNormDomain i → ‖x‖ ≤ Bs)
    (hParentJets : ∀ owner i k y, y ∈ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i →
      ‖iteratedFDeriv ℝ k (outer owner ∘ ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).symm)
        ((parameterTensorModelEquiv (m+1) d).symm y)‖ ≤ Parent k)
    (rho transitionBound : ℝ) (hT : 0 ≤ transitionBound) (labelBound : ℕ)
    (label : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℕ)
    (hLabel : ∀ nu, label nu ≤ labelBound) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let positive := repairReferencePositiveData raw rho
    let base := repairReferenceSignedHierarchy b.cover b.operatorBound transitionBound
    let weight := fun nu => base^label nu
    let cap := base^labelBound
    let data := repairReferenceWeightedData positive weight
    RepairOriginalTransitionBudgets raw Parameter Spatial →
    ∀ j, parameterRound2_originalFixedPacketProfile data j 1 ≠ ⊤ ∧
      (j ≤ J → (parameterRound2_originalFixedPacketProfile data j 1).toReal ≤
        repairReferenceOriginalFixedProfile b cap Bs R Parent Parameter Spatial j) := by
  let actualR := repairReferenceCompletedMapProfile seed S J R
  have hActual : ∀ j, 0 ≤ actualR j := repairReferenceCompletedMapProfile_nonneg seed S J R hR
  have hAllMap (j : ℕ) := repair_reference_completed_map_bound seed hseed hFjoint S hSO hCompact J R hMap (j+2)
  have hBudget := repair_reference_actual_factory_fixed_budget b seed hF Htensor S O K center family
    hseed hFjoint hOpen hSO hSample hSEval outer hOuter hSupport actualR Parent Parameter Spatial
    hActual hParent hParameter hSpatial hAllMap Bs hBs hRadius hParentJets
    rho transitionBound hT labelBound label hLabel
  intro raw positive base weight cap data transition j
  have hb := hBudget transition j
  refine ⟨hb.1,?_⟩
  intro hj
  exact hb.2.trans_eq (repairReferenceOriginalFixedProfile_prefix b cap Bs actualR R Parent Parameter Spatial j (by
    intro k hk
    exact if_pos (show k ≤ J+2 by omega)))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_actual_factory_finite_fixed_budget
