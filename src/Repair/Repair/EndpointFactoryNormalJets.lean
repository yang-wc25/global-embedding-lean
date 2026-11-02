import Repair.EndpointFactoryLinearInputs
import Repair.EndpointObserverCoordinateJets

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


def repairReferenceNormalNativeProfile (b : RepairReferenceFactoryBudget m d N)
    (R : ℕ → ℝ) (j : ℕ) : ℝ :=
  round4NativeNormalHostConstant m N j b.firstReserve b.transverseReserve b.forward b.inverse
    (actualOriginalMapJetCost (m+1) d N j*R (j+2))

theorem repairReferenceNormalNativeProfile_nonneg
    (b : RepairReferenceFactoryBudget m d N) (R : ℕ → ℝ) (j : ℕ) :
    0 ≤ repairReferenceNormalNativeProfile b R j := by
  apply round4NativeNormalHostConstant_nonneg
  have h := b.cover.covectorBound_pos
  dsimp only [RepairReferenceFactoryBudget.forward]
  positivity

def repairReferenceNormalOriginalProfile (b : RepairReferenceFactoryBudget m d N)
    (R T : ℕ → ℝ) (j : ℕ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap‖ *
    repairEntranceCompositionProfile (repairReferenceNormalNativeProfile b R) T j *
    ‖(parameterTensorModelEquiv (m+1) d).symm.toContinuousLinearMap‖^j

theorem repairReferenceNormalOriginalProfile_nonneg
    (b : RepairReferenceFactoryBudget m d N) (R T : ℕ → ℝ)
    (hT : ∀ j, 0 ≤ T j) (j : ℕ) : 0 ≤ repairReferenceNormalOriginalProfile b R T j := by
  have h := repairEntranceCompositionProfile_nonneg (repairReferenceNormalNativeProfile b R)
    T (repairReferenceNormalNativeProfile_nonneg b R) hT j
  unfold repairReferenceNormalOriginalProfile
  positivity

include hF Htensor O K center in
/-- Jets of the same Round4-produced normal in the literal original full
joint coordinates. Only the original map prefix through j+2 is used in
the native profile, followed by actual original coordinate transitions. -/
theorem repair_reference_original_family_normal_jets
    (hseed : RepairReferenceSeedDomains seed)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (R T : ℕ → ℝ) (hR : ∀ j, 0 ≤ R j) (hT : ∀ j, 0 ≤ T j)
    (hMap : ∀ j, paperAtlasCj (j+2)
      (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S ≤ ENNReal.ofReal (R (j+2)))
    (nu : Fin (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).primaryCount)
    (i : Fin seed.atlas.count × Fin seed.parameterCount)
    (y : Fin (m+1+d) → ℝ)
    (hy : y ∈ incrementsOriginalPrimaryDifferentiation
      (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer) nu i)
    (hTransition : ∀ k, 1 ≤ k →
      let ix := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      let owner := (seed.parameterChart ix.1.2).prod (seed.atlas.chart ix.1.1)
      let observer := (seed.parameterChart i.2).prod (seed.atlas.chart i.1)
      ‖iteratedFDeriv ℝ k (owner ∘ observer.symm)
        ((parameterTensorModelEquiv (m+1) d).symm y)‖ ≤ T k)
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart
      ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).freeNormal nu) i) y‖ ≤
        repairReferenceNormalOriginalProfile b R T j := by
  let data := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
  let ix := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
  let owner := (seed.parameterChart ix.1.2).prod (seed.atlas.chart ix.1.1)
  let observer := (seed.parameterChart i.2).prod (seed.atlas.chart i.1)
  let xi := (b.cover.template ((family ix.1).pick ix.2.1)).covectors ix.2.2
  let actual := (family ix.1).actualNormal ix.2.1 ix.2.2
  let localField := repairReferenceActualNormalCoordinates seed hF
    (seed.parameterChart ix.1.2) (seed.atlas.chart ix.1.1) xi actual
  let W := repairReferenceActualNormalCarrier seed hF
    (seed.parameterChart ix.1.2) (seed.atlas.chart ix.1.1) xi actual
  let U := data.primaryDomain nu
  let a := parameterTensorModelEquiv (m+1) d
  have ho : owner ∈ IsManifold.maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hseed.parameter_charts_smooth ix.1.2)
      (hseed.atlas_smooth.chart_mem ix.1.1)
  have he : observer ∈ IsManifold.maximalAtlas 𝓘(ℝ,X) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (hseed.parameter_charts_smooth i.2)
      (hseed.atlas_smooth.chart_mem i.1)
  have hU : IsOpen U := repair_reference_actual_normal_domain_open seed hF _ _ xi actual
  have hW : IsOpen W := round4NormalCutoffCarrier_open _ _ _
  have hDomain : U ⊆ owner.source ∩ owner ⁻¹' W := Subset.rfl
  have hField : ∀ z ∈ U, data.freeNormal nu z = localField (owner z) := fun _ _ => rfl
  have hs : ContDiffOn ℝ ∞ localField W :=
    repair_reference_actual_normal_coordinates_smooth seed hF _ _ xi actual
  have hz : a.symm y ∈ observer.target := ⟨hy.1.2,hy.1.1⟩
  have hzU : observer.symm (a.symm y) ∈ U := hy.2
  have hjet := repair_local_field_observer_jet owner observer ho he (data.freeNormal nu)
    localField U W hU hW hField hDomain hs (repairReferenceNormalNativeProfile b R) T
    (repairReferenceNormalNativeProfile_nonneg b R) hT (a.symm y) hz hzU (by
      intro k
      exact (family ix.1).normal_jets k (R (k+2)) (hR _) (hMap k)
        ix.2.1 ix.2.2 k le_rfl _ ((hDomain hzU).2)) hTransition j
  have hreg := repair_local_field_observer_smooth owner observer ho he
    (data.freeNormal nu) localField U W hU hField hDomain hs
  have hcoord := repair_original_output_coordinate_jet a
    (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap (data.freeNormal nu ∘ observer.symm)
    (observer.target ∩ observer.symm ⁻¹' U) (observer.symm.isOpen_inter_preimage hU)
    hreg y ⟨hz,hzU⟩ j _ hjet
  exact hcoord

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_normal_jets
