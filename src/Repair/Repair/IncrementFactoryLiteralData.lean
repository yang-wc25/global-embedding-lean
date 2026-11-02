import Repair.IncrementRegionFactory
import Repair.ReferenceOriginalLocalFactoryDomains

/-! The literal phase datum is produced from the SAME weighted positive
actual local factory family. Owner sampling and original template
membership are proved from its actual normal carrier. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance factoryLiteralRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance factoryLiteralSquareNormed {E : Type*}
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
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)

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
  (hseed : RepairReferenceSeedDomains seed)
  (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)


include hF Htensor O K center in
theorem increment_actual_factory_literal_phase_data
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (hSEval : ∀ i, S i ⊆ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i)
    (rho T : ℝ) (labelBound : ℕ)
    (label : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℕ)
    (hLabel : ∀ nu, label nu ≤ labelBound)
    (hProper : ∀ nu mu, nu ≠ mu →
      (tsupport ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).cutoff nu) ∩
        tsupport ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).cutoff mu)).Nonempty →
        label nu ≠ label mu) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let weight := fun nu => repairReferenceSignedHierarchy b.cover b.operatorBound T ^ label nu
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    Nonempty (IncrementActualLiteralPhaseData data b.cover b.operatorBound T labelBound) := by
  intro raw weight data
  let ix := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s)
  refine ⟨{ owner := fun nu => (ix nu).1.1
            index := fun nu => (family (ix nu).1).pick (ix nu).2.1
            edge := fun nu => (ix nu).2.2
            label := label
            label_le := hLabel
            phase_eq := fun nu => rfl
            source := ?_
            owner_samples := ?_
            operator := ?_
            proper := hProper }⟩
  · intro nu z hz
    exact (repair_reference_original_family_operator b seed hF Htensor S O K center family hseed outer nu z hz).1
  · intro nu z hz
    exact (repair_reference_original_family_owner_samples b seed hF Htensor S O K center family hseed outer
      hSample hSEval nu z hz).2.1
  · intro nu z hz
    exact (repair_reference_original_family_operator b seed hF Htensor S O K center family hseed outer nu z hz).2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_factory_literal_phase_data
