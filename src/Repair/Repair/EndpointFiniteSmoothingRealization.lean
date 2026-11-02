import Repair.EndpointActualFixedBudget
import Repair.EndpointFiniteFixedBudget
import Repair.EndpointSmoothingGeometry
import Repair.EntranceFiniteOriginalClass
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



include hF Htensor O K center in
theorem repair_original_factory_smoothing_from_finite_class
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
    (hSourceRadius : ∀ i x, x ∈ seed.sourceNormDomain i → ‖x‖ ≤ Bs)
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
    ∀ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data)
      (hAll : data.parameterSet=univ)
      (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ) (radius : ℝ) (hRadius : 0 < radius)
      (geometry : RepairOriginalSmoothingGeometry data BS TS BP TP Ds Dp radius),
    ∃ packet : Round3RepairFixedSmoothingPacket data BS TS BP TP Ds Dp radius hRadius
      (repairOriginalActualReferenceProfile data) (repairOriginalActualGivenProfile data),
      packet.referenceMap=data.F ∧ packet.Omega=data.sourceNormDomain ∧
      packet.Q=data.parameterNormDomain ∧
      packet.sourcePreparation.raw=geometry.sourcePreparation.raw ∧
      packet.parameterPreparation.raw=geometry.parameterPreparation.raw ∧
      (∀ j, j ≤ J → (parameterRound2_originalFixedPacketProfile data j 1).toReal ≤
        repairReferenceOriginalFixedProfile b cap Bs R Parent Parameter Spatial j) := by
  intro raw positive base weight cap data transitions hd hs hAll BS TS BP TP Ds Dp radius hRadius geometry
  have budget := repair_reference_actual_factory_finite_fixed_budget b seed hF Htensor S O K center family
    hseed hFjoint hOpen hSO hSample hSEval outer hOuter hSupport J R Parent Parameter Spatial
    hR hParent hParameter hSpatial hCompact hMap Bs hBs hSourceRadius hParentJets
    rho transitionBound hT labelBound label hLabel transitions
  let packet := repair_original_actual_smoothing_packet data hd hs hOpen hAll
    BS TS BP TP Ds Dp radius hRadius geometry rfl rfl (fun j => (budget j).1)
  exact ⟨packet,rfl,rfl,rfl,rfl,rfl,fun j hj => (budget j).2 hj⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_original_factory_smoothing_from_finite_class
