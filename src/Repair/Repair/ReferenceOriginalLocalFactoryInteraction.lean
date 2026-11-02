import Repair.ReferenceOriginalLocalFactoryPlateauJets
import Repair.ReferenceOriginalInteractionParent
import Repair.ReferenceWeightedNativeData

/-! The actual same-factory secondary domains and their numerical common
buffer. The plateaus, their common C1 bound, and the parent collar are
produced here, not assumed to be completed secondary geometry. -/

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


def repairReferenceFactoryInteractionDerivative
    (b : RepairReferenceFactoryBudget m d N) (T : ℕ → ℝ) : ℝ :=
  repairEntranceCompositionProfile (repairReferenceFactoryPlateauProfile b) T 1

def repairReferenceFactoryInteractionBuffer
    (b : RepairReferenceFactoryBudget m d N) (T : ℕ → ℝ) : ℝ :=
  repairReferenceInteractionBuffer b.buffer (repairReferenceFactoryInteractionDerivative b T)

theorem repairReferenceFactoryInteractionBuffer_pos
    (b : RepairReferenceFactoryBudget m d N) (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) :
    0 < repairReferenceFactoryInteractionBuffer b T :=
  repair_reference_interaction_buffer_pos b.buffer_pos
    (repairEntranceCompositionProfile_nonneg _ _ (repairReferenceFactoryPlateauProfile_nonneg b) hT 1)

include hF Htensor O K center in
theorem repair_reference_original_factory_interaction_geometry
    (hseed : RepairReferenceSeedDomains seed)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (outer theta : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hThetaSource : ∀ i, tsupport (theta i) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).source ∩
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)) ⁻¹' K i)
    (hO : ∀ i, IsOpen (O i))
    (hK : ∀ i, K i ⊆ closedBall (center i) b.modelRadius)
    (hBuffer : ∀ i z, z ∈ K i → ball z b.buffer ⊆ O i)
    (B0 : ℝ) (hCenter : ∀ i, ‖center i‖ ≤ B0)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTransition : ∀ nu i z, z ∈ O i → ∀ j, 1 ≤ j →
      let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      let owner := (seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)
      let observer := (seed.parameterChart i.2).prod (seed.atlas.chart i.1)
      observer.symm z ∈ owner.source → ‖iteratedFDeriv ℝ j (owner ∘ observer.symm) z‖ ≤ T j)
    (rho : ℝ) (weight : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℝ) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    ∀ (hd : IncrementsOriginalDomainConditions data)
      (hOOpen : ∀ i, O i ⊆ actualOriginalNativeOpen data i)
      (hInner : ∀ i z, z ∈ O i → (seed.atlas.chart i.1).symm z.2 ∈ seed.atlas.inner i.1)
      (hEval : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈
        incrementsOriginalEvaluation seed.atlas seed.parameterChart seed.sourceNormDomain
          seed.parameterNormDomain seed.parameterSet i),
      ∀ (r : ActualSecondarySignedRecord (Fin data.primaryCount)) (i : Fin seed.atlas.count × Fin seed.parameterCount),
        Nonempty (RepairReferenceActualInteractionGeometry data i r
          ((seed.parameterChart i.2).target ×ˢ (univ : Set M))
          (round3ParameterNativeParent (seed.parameterChart i.2) (theta i)) b.modelRadius
          (repairReferenceFactoryInteractionBuffer b T)
          (B0+b.modelRadius+repairReferenceFactoryInteractionBuffer b T)) := by
  intro raw data hd hOOpen hInner hEval r i
  have hCollar := repair_reference_original_parent_collar data hd i (theta i) (hCompact i)
    (hSmooth i) (K i) (O i) (center i) b.modelRadius b.buffer (hThetaSource i) (hK i) (hBuffer i)
  have hProperties := repair_reference_original_family_plateau_properties
    b seed hF Htensor S O K center family hseed hSO hSample outer
  apply repair_reference_actual_original_interaction_geometry b.buffer
    (repairReferenceFactoryInteractionDerivative b T) b.modelRadius B0 b.buffer_pos
    (repairEntranceCompositionProfile_nonneg _ _ (repairReferenceFactoryPlateauProfile_nonneg b) hT 1)
    data hd i r (round3ParameterNativeParent (seed.parameterChart i.2) (theta i)) hCollar.1
    (repairReferenceOriginalFamilyPlateau b seed hF Htensor S O K center family)
    (fun nu => (hProperties nu).2.1) (fun nu => (hProperties nu).2.2.1)
    (fun nu z hz => ((hProperties nu).2.2.2 z hz).eq_of_nhds)
    (O i) (hO i) (hOOpen i) (hInner i) (hEval i) _ hCollar.2.1 (center i) (hCenter i) hCollar.2.2
  intro nu z hz
  have hh := repair_reference_original_family_plateau_observer_jets b seed hF Htensor S O K center family
    hseed hSO hSample T hT nu i z
    (repair_reference_original_native_joint_target seed S hSO i z (hSample i z hz))
    (hTransition nu i z hz) 1
  rw [norm_iteratedFDeriv_one] at hh
  exact hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_original_factory_interaction_geometry
